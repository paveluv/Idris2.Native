||| Closed compiled expressions evaluated when a program is compiled
||| (`evaluate`): a function of the program applied to values, computed to
||| its value, as the program would compute it at run time.
|||
||| It evaluates Idris's compiled form of each definition (`NamedCExp`),
||| the one every code generator is given (`namedDefs` of the program's
||| `CompileData`): types and proofs erased, interfaces' methods inlined
||| where Idris inlines them. It is strict, as
||| the compiled code is, but for what the code delays (`NmDelay`), which is
||| evaluated where it is forced, and a constant is evaluated once, as the
||| compiled code shares it, in steps of its own. A primitive operation
||| means what Idris says it does (`getOp`). A maker of an object from
||| words, and the primitive that reads one, mean what their marks say
||| (`Meanings`), not what their bodies do. An expression that only the
||| running program can compute, a foreign function, a crash, a constant
||| that needs its own value, or one that takes more steps than the fuel,
||| is not computed, and says why.
|||
||| Part of the code generator, which uses it for the tables
||| (`Native.Codegen.Tabulate`) and the constants a program marks static
||| (`constants`).
module Native.Codegen.Evaluate

import Compiler.CompileExpr
import Core.CompileExpr
import Core.Context
import Core.Context.Context
import Core.Core
import Core.FC
import Core.Name
import Core.Name.Scoped
import Core.Primitives
import Core.TT
import Core.TT.Primitive
import Core.Value
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Data.String
import Data.Vect
import Data.Zippable
import Libraries.Data.WithDefault
import Native.Primitive
import Native.Types.FromWords
import Native.Types.PureLoad

%default covering

||| A value as the evaluation has it: a constant, a constructor with its
||| fields, a function with the values it closes over or the arguments it
||| has so far, a delayed expression, an erased one, or an object made of
||| words.
public export
data Value : Type where
  VConst : Constant -> Value
  VCon : Name -> (tag : Maybe Int) -> List Value -> Value
  ||| A lambda, with the variables in scope where it was made.
  VLam : List (Name, Value) -> Name -> NamedCExp -> Value
  ||| A definition applied to fewer arguments than it takes.
  VPartial : Name -> List Value -> Value
  VDelay : List (Name, Value) -> NamedCExp -> Value
  VErased : Value
  ||| The object a maker made (`Types.FromWords`): its payload's words, each
  ||| at its index from 0, so that a read of one does not walk the words
  ||| before it.
  VBytes : SortedMap Int Bits64 -> Value

||| The label of the steps left, which bounds an evaluation.
data Steps : Type where

||| The compiled forms of the definitions and of everything they call, as
||| their modules keep them, or compiled now: for functions that the program's compilation does not
||| reach from `main`, such as a table only the runtime's flat code reads.
||| Called while the context still holds the definitions, before
||| `getCompileData`, which puts it back as it found it.
export
compileFor : {auto c : Ref Ctxt Defs} -> List Name -> Core (SortedMap Name NamedDef)
compileFor ns = go ns empty
  where
    -- the definitions an expression refers to
    refs : NamedCExp -> List Name
    refs (NmRef _ n) = [n]
    refs (NmLam _ _ b) = refs b
    refs (NmLet _ _ v b) = refs v ++ refs b
    refs (NmApp _ f as) = refs f ++ concatMap refs as
    refs (NmCon _ _ _ _ as) = concatMap refs as
    refs (NmOp _ _ as) = concatMap refs (toList as)
    refs (NmExtPrim _ _ as) = concatMap refs as
    refs (NmForce _ _ x) = refs x
    refs (NmDelay _ _ x) = refs x
    refs (NmConCase _ sc alts def) =
      refs sc ++ concatMap (\(MkNConAlt _ _ _ _ b) => refs b) alts ++ maybe [] refs def
    refs (NmConstCase _ sc alts def) =
      refs sc ++ concatMap (\(MkNConstAlt _ b) => refs b) alts ++ maybe [] refs def
    refs _ = []

    defRefs : NamedDef -> List Name
    defRefs (MkNmFun _ b) = refs b
    defRefs (MkNmError b) = refs b
    defRefs _ = []

    go : List Name -> SortedMap Name NamedDef -> Core (SortedMap Name NamedDef)
    go [] done = pure done
    go (n :: rest) done =
      if isJust (lookup n done) then go rest done else do
        Just g <- lookupCtxtExact n (gamma !(get Ctxt))
          | Nothing => go rest done
        -- a module's TTC keeps its definitions' compiled forms; one of this
        -- module's may not be compiled yet
        cd <- case compexpr g of
          Just cd => pure (Just cd)
          Nothing => do
            compileDef n
            Just g' <- lookupCtxtExact n (gamma !(get Ctxt))
              | Nothing => pure Nothing
            pure (compexpr g')
        case cd of
          Nothing => go rest done
          Just cd' => let d = forgetDef cd' in go (defRefs d ++ rest) (insert n d done)

||| What the evaluation takes a call of a definition to mean other than by
||| its body: the makers of an object from words (`Types.FromWords`), each
||| found by its mark, whose call is the object of the words its function
||| gives; and the backend's primitives (`Native.Primitive`), of which the
||| one that reads such an object (`PayloadWord`) is the object's word. Both
||| bodies reach what only the running program does, a buffer's foreign
||| functions, where the meanings need none.
public export
record Meanings where
  constructor MkMeanings
  makers : SortedSet Name
  primitives : SortedMap Name Primitive

||| A constant as the evaluation has it so far: being evaluated, or its
||| value.
data Memoised = InProgress | Evaluated Value

||| The label of the constants evaluated so far, which every evaluation
||| that reads one after shares.
data Memo : Type where

||| Whether Idris inlines a definition at each use, when the module that
||| uses it is built: one not marked `%noinline` that is marked `%inline`,
||| or is `public export` with a body Idris's heuristic takes for simple,
||| which of a constant is a name, a literal, an erased value or a
||| constructor of no fields, and of a function also one constructor,
||| operation or call of its variables. Its uses are then its body, and no
||| call of its name is left for a meaning of the name to answer.
export
inlined : GlobalDef -> Bool
inlined g = elem Inline (flags g) && not (elem NoInline (flags g))

||| What stops Idris inlining a definition it inlines (`inlined`). The
||| heuristic inlines only a `public export` one, so of any other the cause
||| is its `%inline`, to remove. Of a `public export` one, the cause is its
||| `%inline`, if it has one, which `%noinline` may not join, or else the
||| heuristic, which `export` or `%noinline` stops.
export
inliningFix : GlobalDef -> String
inliningFix g = case collapseDefault (visibility g) of
  Public => "remove its %inline, or, if it has none, make it export or mark it %noinline"
  _ => "remove its %inline"

||| An evaluation over the program's compiled definitions: the function
||| that evaluates a definition applied to arguments, in at most `fuel`
||| steps, to its value, or says why it is not computed. A constant is
||| evaluated once, on the first read of it, in at most `fuel` steps of its
||| own, as the compiled code computes it once, and no read of it is
||| charged those steps: so whether an evaluation has the steps it needs
||| depends neither on which evaluations came before it nor on how often it
||| reads a constant. One that needs its own value is not computed.
evaluation : Meanings -> (compiled : SortedMap Name NamedDef) -> (fuel : Nat) ->
             Core (Name -> List Value -> Core (Either String Value))
evaluation meanings compiled fuel = do
  s <- newRef Steps 0
  m <- newRef Memo (the (SortedMap Name Memoised) empty)
  pure (\n, as => do
          put Steps fuel
          catch (Right <$> global EmptyFC n as)
                (\err => case err of
                           GenericMsg _ msg => pure (Left msg)
                           _ => throw err))
  where
    -- an error of a definition's body, said to be in it, once, at the innermost
    within : Name -> Error -> Core a
    within n' (GenericMsg fc msg) =
      throw (GenericMsg fc (if isInfixOf ", in " msg then msg else msg ++ ", in " ++ show n'))
    within _ err = throw err

    stuck : FC -> String -> Core a
    stuck fc what = throw (GenericMsg fc ("not computable when the program is compiled: " ++ what))

    -- so many steps taken, if so many are left
    charge : Ref Steps Nat => FC -> Nat -> Core ()
    charge fc k = do
      left <- get Steps
      if left < k then stuck fc "it takes more steps than the evaluation allows"
        else put Steps (minus left k)

    tick : Ref Steps Nat => FC -> Core ()
    tick fc = charge fc 1

    compiledForm : FC -> Name -> Core NamedDef
    compiledForm fc n' =
      maybe (stuck fc ("the definition " ++ show n' ++ ", which the program does not compile")) pure
                           (lookup n' compiled)

    -- the word of a maker's object at an index and a displacement, in
    -- words: the word at their sum, which the machine's load gives too;
    -- outside the words, where the load gives any word, not computed
    payloadWord : FC -> List Value -> Core Value
    payloadWord fc [VBytes ws, VConst (I i), VConst (I d)] =
      let k = cast {to = Integer} i + cast d
          count = wordCount ws in
      case (if k < 0 || k >= count then Nothing else lookup (cast k) ws) of
        Just w => pure (VConst (B64 w))
        Nothing =>
          stuck fc ("a read of word " ++ show k ++ " of an object of " ++ show count ++ " words")
      where
        -- how many words an object has, at 0 to the last
        wordCount : SortedMap Int Bits64 -> Integer
        wordCount ws' = maybe 0 (\last => cast {to = Integer} (fst last) + 1) (rightMost ws')
    payloadWord fc _ = stuck fc "a read of a word of an object no maker made"

    mutual
      eval : Ref Steps Nat => Ref Memo (SortedMap Name Memoised) =>
             List (Name, Value) -> NamedCExp -> Core Value
      eval env (NmLocal fc x) = maybe (stuck fc ("the unbound " ++ show x)) pure (lookup x env)
      eval env (NmRef fc n') = global fc n' []
      eval env (NmLam _ x b) = pure (VLam env x b)
      eval env (NmLet fc x v b) = do tick fc; v' <- eval env v; eval ((x, v') :: env) b
      eval env (NmApp fc (NmRef _ n') as) = do tick fc; global fc n' !(traverse (eval env) as)
      eval env (NmApp fc f as) = do tick fc
                                    f' <- eval env f
                                    applyAll fc f' !(traverse (eval env) as)
      eval env (NmCon _ n' _ tag as) = VCon n' tag <$> traverse (eval env) as
      eval env (NmOp fc op as) = do tick fc; prim fc op !(traverseVect (eval env) as)
      eval env (NmExtPrim fc p _) = stuck fc ("the external primitive " ++ show p)
      eval env (NmForce fc _ x) = force fc !(eval env x)
      eval env (NmDelay _ _ x) = pure (VDelay env x)
      eval env (NmConCase fc sc alts def) = do tick fc; conCase fc env !(eval env sc) alts def
      eval env (NmConstCase fc sc alts def) = do tick fc; constCase fc env !(eval env sc) alts def
      eval env (NmPrimVal _ k) = pure (VConst k)
      eval env (NmErased _) = pure VErased
      eval env (NmCrash fc msg) = stuck fc ("a crash: " ++ msg)

      -- a definition applied to arguments: what it means, if the meanings
      -- say (a maker's object, the payload word), else its body; at as
      -- many arguments as it takes, its result applied to the rest if more,
      -- a partial application if fewer
      global : Ref Steps Nat => Ref Memo (SortedMap Name Memoised) =>
               FC -> Name -> List Value -> Core Value
      global fc n' as =
        if contains n' meanings.makers then meant fc n' Types.FromWords.arity (made fc n') as
        else
        case lookup n' meanings.primitives of
          Just Primitive.PayloadWord =>
            meant fc n' (Types.PureLoad.arity (Primitive.signature Primitive.PayloadWord))
              (payloadWord fc) as
          _ => case !(compiledForm fc n') of
            MkNmFun [] b => applyAll fc !(constant fc n' b) as
            MkNmFun ps b =>
              if length as < length ps then pure (VPartial n' as) else do
                r <- catch (eval (reverse (zip ps as)) b) (within n')
                applyAll fc r (drop (length ps) as)
            MkNmCon tag arity nt =>
              if length as < arity then pure (VPartial n' as) else
                case nt of
                  Just i => maybe (stuck fc ("the newtype " ++ show n')) pure (getAt i as)
                  Nothing => pure (VCon n' tag (take arity as))
            MkNmForeign {} => stuck fc ("the foreign function " ++ show n')
            MkNmError e => catch (eval [] e) (within n')

      -- a definition of so many arguments that means a function of them
      -- applied to arguments: the function at as many as it takes, its
      -- result applied to the rest; a partial application if fewer
      meant : Ref Steps Nat => Ref Memo (SortedMap Name Memoised) =>
              FC -> Name -> (arity : Nat) -> (List Value -> Core Value) -> List Value -> Core Value
      meant fc n' arity meaning as =
        if length as < arity then pure (VPartial n' as)
        else applyAll fc !(meaning (take arity as)) (drop arity as)

      -- a constant's value: the first read evaluates its body, in steps of
      -- its own, after which the reader has the steps it had, and every
      -- later read has its value; one that needs its own value is not
      -- computed. A failure leaves it unevaluated, so that each that
      -- reads it after says why.
      constant : Ref Steps Nat => Ref Memo (SortedMap Name Memoised) =>
                 FC -> Name -> NamedCExp -> Core Value
      constant fc n' b = case lookup n' !(get Memo) of
        Just (Evaluated v) => pure v
        Just InProgress => stuck fc ("the constant " ++ show n' ++ ", which needs its own value")
        Nothing => do
          update Memo (insert n' InProgress)
          readerSteps <- get Steps
          put Steps fuel
          v <- catch (eval [] b) (\err => do update Memo (delete n'); within n' err)
          put Steps readerSteps
          update Memo (insert n' (Evaluated v))
          pure v

      -- a maker's call (`Types.FromWords`) at a count and a function: the
      -- object of the function's words at 0, 1, ..., `n - 1`, each a step,
      -- none if `n` is not positive. The words' steps are charged before
      -- any word is made, so that a count the steps do not allow ends the
      -- evaluation before its object takes the memory of that many words.
      made : Ref Steps Nat => Ref Memo (SortedMap Name Memoised) =>
             FC -> Name -> List Value -> Core Value
      made fc n' [VConst (I n), f] = do
        charge fc (cast n)
        VBytes <$> fill 0 empty
        where
          fill : Int -> SortedMap Int Bits64 -> Core (SortedMap Int Bits64)
          fill i acc =
            if i >= n then pure acc else do
              VConst (B64 w) <- applyAll fc f [VConst (I i)]
                | _ => stuck fc ("word " ++ show i ++ " of " ++ show n' ++ ", which is no Bits64")
              fill (i + 1) (insert i w acc)
      made fc n' _ = stuck fc ("a call of the maker " ++ show n' ++ " at a count that is no Int")

      applyAll : Ref Steps Nat => Ref Memo (SortedMap Name Memoised) =>
                 FC -> Value -> List Value -> Core Value
      applyAll fc f [] = pure f
      applyAll fc (VLam env x b) (a :: as) = do r <- eval ((x, a) :: env) b; applyAll fc r as
      applyAll fc (VPartial n' bs) as = global fc n' (bs ++ as)
      applyAll fc VErased _ = pure VErased
      applyAll fc _ _ = stuck fc "the application of a value that is not a function"

      force : Ref Steps Nat => Ref Memo (SortedMap Name Memoised) =>
              FC -> Value -> Core Value
      force fc (VDelay env x) = eval env x
      force fc v = pure v

      conCase : Ref Steps Nat => Ref Memo (SortedMap Name Memoised) =>
                FC -> List (Name, Value) -> Value -> List NamedConAlt -> Maybe NamedCExp ->
                Core Value
      conCase fc env (VCon n' _ fs) alts def = case find (\(MkNConAlt c _ _ _ _) => c == n') alts of
        Just (MkNConAlt _ _ _ xs b) => eval (reverse (zip xs fs) ++ env) b
        Nothing => maybe (stuck fc ("no alternative for " ++ show n')) (eval env) def
      -- an erased value has one constructor, whose fields are erased too
      conCase fc env VErased [MkNConAlt _ _ _ xs b] _ = eval (map (\x => (x, VErased)) xs ++ env) b
      conCase fc env _ _ _ = stuck fc "a case on a value that is no constructor"

      constCase : Ref Steps Nat => Ref Memo (SortedMap Name Memoised) =>
                  FC -> List (Name, Value) -> Value -> List NamedConstAlt -> Maybe NamedCExp ->
                  Core Value
      constCase fc env (VConst k) alts def = case find (\(MkNConstAlt k' _) => k' == k) alts of
        Just (MkNConstAlt _ b) => eval env b
        Nothing => maybe (stuck fc ("no alternative for " ++ show k)) (eval env) def
      constCase fc env _ _ _ = stuck fc "a case on a value that is no constant"

      prim : FC -> PrimFn arity -> Vect arity Value -> Core Value
      prim fc BelieveMe [_, _, x] = pure x
      prim fc Crash _ = stuck fc "a crash"
      prim fc op vs = case asConstants vs of
        Nothing => stuck fc ("the primitive " ++ show op ++ " of a value that is no constant")
        Just ks => case getOp {vars = Scope.empty} op (map (NPrimVal fc) ks) of
          Just (NPrimVal _ k) => pure (VConst k)
          _ => stuck fc ("the primitive " ++ show op ++ " of " ++ show (toList ks))
        where
          asConstants : Vect len Value -> Maybe (Vect len Constant)
          asConstants [] = Just []
          asConstants (VConst k :: xs) = (k ::) <$> asConstants xs
          asConstants _ = Nothing

||| The values of the function at each argument list, each evaluation of at
||| most `fuel` steps, over the program's compiled definitions and the
||| meanings, the constants they read evaluated once for all, each in at
||| most `fuel` steps of its own; or why the first that is not computed is
||| not.
export
evaluate : Meanings -> (compiled : SortedMap Name NamedDef) -> (fuel : Nat) -> Name ->
           List (List Value) -> Core (Either String (List Value))
evaluate meanings compiled fuel n calls = values !(evaluation meanings compiled fuel) calls [<]
  where
    values : (Name -> List Value -> Core (Either String Value)) -> List (List Value) ->
             SnocList Value -> Core (Either String (List Value))
    values call [] acc = pure (Right (acc <>> []))
    values call (as :: rest) acc = case !(call n as) of
      Left err => pure (Left err)
      Right v => values call rest (acc :< v)

||| The value of each constant, in at most `fuel` steps of its own, over the
||| program's compiled definitions and the meanings, the constants they read
||| evaluated once for all, each in at most `fuel` steps of its own too, so
||| that whether a constant has the steps it needs does not depend on the
||| order of the constants; or why it is not computed.
export
constants : Meanings -> (compiled : SortedMap Name NamedDef) -> (fuel : Nat) -> List Name ->
            Core (List (Name, Either String Value))
constants meanings compiled fuel ns = do
  call <- evaluation meanings compiled fuel
  traverse (\n => (n,) <$> call n []) ns
