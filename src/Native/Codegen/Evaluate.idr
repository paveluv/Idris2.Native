||| Closed compiled expressions evaluated when a program is compiled
||| (`evaluate`): a function of the program applied to values, computed to
||| its value, as the program would compute it at run time.
|||
||| It evaluates Idris's compiled form of each definition (`NamedCExp`),
||| the one every code generator is given (`namedDefs` of the program's
||| `CompileData`): types and proofs erased, interfaces' methods inlined
||| where Idris inlines them. It is strict, as
||| the compiled code is, but for what the code delays (`NmDelay`), which is
||| evaluated where it is forced. A primitive operation means what Idris
||| says it does (`getOp`). An expression that only the running program can
||| compute, a foreign function, a crash, or one that takes more steps than
||| the fuel, is not computed, and says why.
|||
||| Part of the code generator, which uses it for the tables
||| (`Native.Codegen.Tabulate`).
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
import Core.TT.Primitive
import Core.Value
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.String
import Data.Vect
import Data.Zippable

%default covering

||| A value as the evaluation has it: a constant, a constructor with its
||| fields, a function with the values it closes over or the arguments it
||| has so far, a delayed expression, or an erased one.
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

||| The values of the function at each argument list, each evaluation of at
||| most `fuel` steps, over the program's compiled definitions; or why one
||| is not computed.
export
evaluate : (compiled : SortedMap Name NamedDef) -> (fuel : Nat) -> Name -> List (List Value) ->
           Core (Either String (List Value))
evaluate compiled fuel n calls = do
  s <- newRef Steps fuel
  catch (Right <$> traverse (\as => do put Steps fuel; global EmptyFC n as) calls)
        (\err => case err of
                   GenericMsg _ msg => pure (Left msg)
                   _ => throw err)
  where
    -- an error of a definition's body, said to be in it, once, at the innermost
    within : Name -> Error -> Core a
    within n' (GenericMsg fc msg) =
      throw (GenericMsg fc (if isInfixOf ", in " msg then msg else msg ++ ", in " ++ show n'))
    within _ err = throw err

    stuck : FC -> String -> Core a
    stuck fc what = throw (GenericMsg fc ("not computable when the program is compiled: " ++ what))

    tick : Ref Steps Nat => FC -> Core ()
    tick fc = case !(get Steps) of
      Z => stuck fc "it takes more steps than the evaluation allows"
      S k => put Steps k

    compiledForm : FC -> Name -> Core NamedDef
    compiledForm fc n' =
      maybe (stuck fc ("the definition " ++ show n' ++ ", which the program does not compile")) pure
                           (lookup n' compiled)

    mutual
      eval : Ref Steps Nat => List (Name, Value) -> NamedCExp -> Core Value
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

      -- a definition applied to arguments: its body if they are as many as
      -- it takes, its result applied to the rest if more, a partial
      -- application if fewer
      global : Ref Steps Nat => FC -> Name -> List Value -> Core Value
      global fc n' as = case !(compiledForm fc n') of
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

      applyAll : Ref Steps Nat => FC -> Value -> List Value -> Core Value
      applyAll fc f [] = pure f
      applyAll fc (VLam env x b) (a :: as) = do r <- eval ((x, a) :: env) b; applyAll fc r as
      applyAll fc (VPartial n' bs) as = global fc n' (bs ++ as)
      applyAll fc VErased _ = pure VErased
      applyAll fc _ _ = stuck fc "the application of a value that is not a function"

      force : Ref Steps Nat => FC -> Value -> Core Value
      force fc (VDelay env x) = eval env x
      force fc v = pure v

      conCase : Ref Steps Nat => FC -> List (Name, Value) -> Value ->
                List NamedConAlt -> Maybe NamedCExp -> Core Value
      conCase fc env (VCon n' _ fs) alts def = case find (\(MkNConAlt c _ _ _ _) => c == n') alts of
        Just (MkNConAlt _ _ _ xs b) => eval (reverse (zip xs fs) ++ env) b
        Nothing => maybe (stuck fc ("no alternative for " ++ show n')) (eval env) def
      -- an erased value has one constructor, whose fields are erased too
      conCase fc env VErased [MkNConAlt _ _ _ xs b] _ = eval (map (\x => (x, VErased)) xs ++ env) b
      conCase fc env _ _ _ = stuck fc "a case on a value that is no constructor"

      constCase : Ref Steps Nat => FC -> List (Name, Value) -> Value ->
                  List NamedConstAlt -> Maybe NamedCExp -> Core Value
      constCase fc env (VConst k) alts def = case find (\(MkNConstAlt k' _) => k' == k) alts of
        Just (MkNConstAlt _ b) => eval env b
        Nothing => maybe (stuck fc ("no alternative for " ++ show k)) (eval env) def
      constCase fc env _ _ _ = stuck fc "a case on a value that is no constant"

      prim : FC -> PrimFn arity -> Vect arity Value -> Core Value
      prim fc BelieveMe [_, _, x] = pure x
      prim fc Crash _ = stuck fc "a crash"
      prim fc op vs = case constants vs of
        Nothing => stuck fc ("the primitive " ++ show op ++ " of a value that is no constant")
        Just ks => case getOp {vars = Scope.empty} op (map (NPrimVal fc) ks) of
          Just (NPrimVal _ k) => pure (VConst k)
          _ => stuck fc ("the primitive " ++ show op ++ " of " ++ show (toList ks))
        where
          constants : Vect len Value -> Maybe (Vect len Constant)
          constants [] = Just []
          constants (VConst k :: xs) = (k ::) <$> constants xs
          constants _ = Nothing
