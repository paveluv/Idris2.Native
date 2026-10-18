||| The flat lowering: a flat form (`Flat.Exp`) to a `Direct` function of
||| the term IR (`Native.Codegen.TermIR.Program`), written in `Build`.
|||
||| A flat value is its layout's registers: a `W64` for each `Word` and an
||| `F64` for each `Dbl`. An integer narrower than 64 bits is held extended
||| to the word, as its type is signed or not, so an operation on it computes
||| on words and wraps the result to the width again, as ordinary code does;
||| a `Char` is its code point. A data type is recognised by its shape
||| (`Flat.Exp.Shape`), which the lowering is given. One of one
||| constructor is its fields' registers in turn; one of several is a tag,
||| the constructor's own, then every constructor's fields' registers in
||| turn, zero for the constructors other than the value's (`placement`).
|||
||| A form becomes a `Direct` function whose parameters are its parameters'
||| registers in turn and whose results are its result's, and which never
||| collects. It is a function of the program, whose term IR is indexed by
||| the encoding of uniform values; flat code holds no uniform value, so the
||| lowering is the same under every encoding but for the inline extern that
||| names the encoding's pointer tag. The functions of the module that
||| implements the runtime's memory may convert between words and addresses
||| (`convertsIn`), which the inline externs on the current continuation need; no
||| other may. A `case` on a sum is a switch on the tag, and one that is not
||| in tail position a join, whose parameters are the case's registers. A
||| call of a form is a `DirectCall`; a call of the form itself in tail
||| position jumps back to its start, so self tail recursion is a loop. The
||| inline externs (`Native.Intrinsic`) lower to the instructions
||| they stand for, and the services' externs to calls of the functions that
||| implement them on the platform, both as the loaded runtime realises the
||| contract (`Forms`); every other `%extern` and `%foreign` primitive
||| (`FPrim`), the operations on strings and the double functions of the C
||| library lower to `Unsupported`.
module Native.Codegen.LowerFlat

import Native.Codegen.IRCommon.Conv as IRCommon
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Pinned as IRCommon
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Codegen.Linkage.ConvertsIn
import Native.Codegen.Linkage.Expansion as Linkage
import Native.Codegen.Linkage.Routine
import Native.Codegen.TermIR.Body
import Native.Codegen.TermIR.Build as TermIR
import Native.Codegen.TermIR.Decls as TermIR
import Native.Codegen.TermIR.Instr
import Native.Codegen.TermIR.IsInt
import Native.Codegen.TermIR.Mem as TermIR
import Native.Codegen.TermIR.Opnd as TermIR
import Native.Codegen.TermIR.Sig as TermIR
import Native.Codegen.TermIR.Var as TermIR
import Native.Codegen.Words

import Core.Name
import Core.TT
import Core.TT.Primitive
import Data.List
import Data.List.Quantifiers
import Data.So
import Data.SortedMap
import Data.Vect
import Decidable.Equality
import Decidable.Equality.Core
import Native.Data.Distinct
import Native.Flat.ConstType
import Native.Flat.Exp as Flat
import Native.HeapObj.ValEnc
import Native.Intrinsic
import Native.Port
import Native.Primitive
import Native.Types.Enc as Types
import Native.Types.Kind

%default covering

------------------------------------------------------------------------------
-- Registers

export
DecEq Flat.Exp.Rep where
  decEq Flat.Exp.Word Flat.Exp.Word = Yes Refl
  decEq Flat.Exp.Dbl Flat.Exp.Dbl = Yes Refl
  decEq Flat.Exp.Uniform Flat.Exp.Uniform = Yes Refl
  decEq Flat.Exp.Word Flat.Exp.Dbl = No (\case Refl impossible)
  decEq Flat.Exp.Word Flat.Exp.Uniform = No (\case Refl impossible)
  decEq Flat.Exp.Dbl Flat.Exp.Word = No (\case Refl impossible)
  decEq Flat.Exp.Dbl Flat.Exp.Uniform = No (\case Refl impossible)
  decEq Flat.Exp.Uniform Flat.Exp.Word = No (\case Refl impossible)
  decEq Flat.Exp.Uniform Flat.Exp.Dbl = No (\case Refl impossible)

||| The type of a register of the representation.
public export
repTy : Flat.Exp.Rep -> IRCommon.Ty enc
repTy Flat.Exp.Word = IRCommon.Ty.W64
repTy Flat.Exp.Dbl = IRCommon.Ty.F64
repTy Flat.Exp.Uniform = IRCommon.Ty.Val

||| The types of a layout's registers.
public export
tys : Flat.Exp.Layout -> List (IRCommon.Ty enc)
tys [] = []
tys (r :: rs) = repTy r :: tys rs

||| The registers of a form's parameters, in turn.
public export
paramsLayout : List Flat.Exp.FlatVar -> Flat.Exp.Layout
paramsLayout [] = []
paramsLayout (p :: ps) = p.layout ++ paramsLayout ps

||| The signature of a form's `Direct` function.
export
formSig : Flat.Exp.FlatDef -> TermIR.Sig enc
formSig fd =
  TermIR.MkSig (Linkage.Routine.flatName fd.name) (IRCommon.Conv.Direct (tys fd.result) False)
    (tys (paramsLayout fd.params)) (Linkage.ConvertsIn.convertsIn fd.name)

------------------------------------------------------------------------------
-- Values

||| A flat value: its layout and its registers.
public export
record Value (enc : Types.Enc) (v : IRCommon.Ty enc -> Type) where
  constructor MkValue
  layout : Flat.Exp.Layout
  regs : All (TermIR.Opnd v) (tys layout)

||| The value of no registers.
export
noRegs : Value enc v
noRegs = MkValue [] []

||| The registers of one value, then of the other.
export
appendValues : Value enc v -> Value enc v -> Value enc v
appendValues (MkValue a xs) (MkValue b ys) = MkValue (a ++ b) (go a xs)
  where
    go : (a' : Flat.Exp.Layout) -> All (TermIR.Opnd v) (tys a') -> All (TermIR.Opnd v) (tys (a' ++ b))
    go [] [] = ys
    go (_ :: rs) (x :: xs') = x :: go rs xs'

export
concatValues : List (Value enc v) -> Value enc v
concatValues = foldr appendValues noRegs

||| A value's first registers, of the layout, and the rest; nothing if it does
||| not start with them.
export
takeRegs : (a : Flat.Exp.Layout) -> Value enc v -> Maybe (All (TermIR.Opnd v) (tys a), Value enc v)
takeRegs [] val = Just ([], val)
takeRegs (r :: rs) (MkValue (r' :: ls) (x :: xs)) = case decEq r r' of
  Yes Refl => do (ys, rest) <- takeRegs rs (MkValue ls xs)
                 Just (x :: ys, rest)
  No _ => Nothing
takeRegs _ _ = Nothing

||| A value's registers as those of the layout, if they are.
export
regsAs : (a : Flat.Exp.Layout) -> Value enc v -> Maybe (All (TermIR.Opnd v) (tys a))
regsAs a val = case takeRegs a val of
  Just (xs, MkValue [] []) => Just xs
  _ => Nothing

||| A value cut into values of the layouts, in turn, if it is made of them.
export
splitBy : List Flat.Exp.Layout -> Value enc v -> Maybe (List (Value enc v))
splitBy [] (MkValue [] []) = Just []
splitBy [] _ = Nothing
splitBy (a :: as) val = do
  (xs, rest) <- takeRegs a val
  (MkValue a xs ::) <$> splitBy as rest

||| The tag of a sum's value: its first register.
export
tagOf : Value enc v -> Maybe (TermIR.Opnd v IRCommon.Ty.W64)
tagOf (MkValue (Flat.Exp.Word :: _) (t :: _)) = Just t
tagOf _ = Nothing

||| A word, the value of one register of an integer type.
export
wordOf : Value enc v -> Maybe (TermIR.Opnd v IRCommon.Ty.W64)
wordOf (MkValue [Flat.Exp.Word] [w]) = Just w
wordOf _ = Nothing

||| A double, the value of one register of `Double`.
export
doubleOf : Value enc v -> Maybe (TermIR.Opnd v IRCommon.Ty.F64)
doubleOf (MkValue [Flat.Exp.Dbl] [f]) = Just f
doubleOf _ = Nothing

||| Zeros for the registers of the layout: what the registers of a sum's
||| other constructors hold.
export
zeros : (a : Flat.Exp.Layout) -> TermIR.Build d c m v l (All (TermIR.Opnd v) (tys a))
zeros [] = pure []
zeros (Flat.Exp.Word :: rs) = (TermIR.Opnd.W 0 ::) <$> zeros rs
zeros (Flat.Exp.Dbl :: rs) = do z <- TermIR.Build.emit1 (TermIR.Instr.FConst 0.0); (z ::) <$> zeros rs
zeros (Flat.Exp.Uniform :: rs) = (TermIR.Opnd.Erased ::) <$> zeros rs

------------------------------------------------------------------------------
-- Shapes

||| Where a constructor's fields lie in a value of its data type: the tag,
||| if the type has several constructors, the registers before the fields,
||| theirs, and those after.
public export
record Placement where
  constructor MkPlacement
  tag : Maybe Int
  before : Flat.Exp.Layout
  own : Flat.Exp.Layout
  after : Flat.Exp.Layout

||| The constructor of the name among a data type's, and where its fields
||| lie. This and `Flat.Exp.sumSlices` are what every place that builds
||| or opens a sum reads.
export
placement : List Flat.Exp.ConShape -> Name -> Maybe (Flat.Exp.ConShape, Placement)
placement [] _ = Nothing
placement [c] n = if c.name == n then Just (c, MkPlacement Nothing [] (Flat.Exp.fieldsLayout c.fields) []) else Nothing
placement cs n = do
  i <- position cs 0
  c <- getAt i cs
  (b, o, a) <- Flat.Exp.sumSlices cs i
  pure (c, MkPlacement (Just c.tag) b o a)
  where
    position : List Flat.Exp.ConShape -> Nat -> Maybe Nat
    position [] _ = Nothing
    position (c :: cs') i = if c.name == n then Just i else position cs' (S i)

||| A constructor's value from its fields' registers: its tag, if its type
||| has several constructors, and zeros for the others' registers.
export
conValue : Placement -> Value enc v -> TermIR.Build d c m v l (Value enc v)
conValue p fs = do
  b <- zeros p.before
  a <- zeros p.after
  let body = appendValues (MkValue p.before b) (appendValues fs (MkValue p.after a))
  pure $ case p.tag of
    Nothing => body
    Just t => appendValues (MkValue [Flat.Exp.Word] [TermIR.Opnd.W (cast t)]) body

||| The registers of a constructor's fields in a value of its data type.
export
fieldsOf : Placement -> Value enc v -> Maybe (Value enc v)
fieldsOf p val = do
  rest <- case p.tag of
    Nothing => Just val
    Just _ => snd <$> takeRegs [Flat.Exp.Word] val
  (_, rest') <- takeRegs p.before rest
  (own, _) <- takeRegs p.own rest'
  pure (MkValue p.own own)

------------------------------------------------------------------------------
-- Calls

||| A form that the program declares as a `Direct` function, as a call of it
||| needs it.
public export
record Callee (d : TermIR.Decls enc) where
  constructor MkCallee
  form : Flat.Exp.FlatDef
  var : (n ** TermIR.Var d.sigs
    (TermIR.MkSig n (IRCommon.Conv.Direct (tys form.result) False) (tys (paramsLayout form.params))
     (convertsIn form.name)))

||| The forms the declarations have `Direct` functions for, by the forms'
||| names.
export
callees : (d : TermIR.Decls enc) -> List Flat.Exp.FlatDef -> SortedMap Name (Callee d)
callees d fds = fromList (mapMaybe one (TermIR.Var.enumerate d.sigs))
  where
    byName : SortedMap Name Flat.Exp.FlatDef
    byName = fromList [(Linkage.Routine.flatName fd.name, fd) | fd <- fds]

    one : (s ** TermIR.Var d.sigs s) -> Maybe (Name, Callee d)
    one (TermIR.MkSig n (IRCommon.Conv.Direct rs False) ps cv ** var) = do
      fd <- lookup n byName
      case (decEq rs (tys fd.result),
            decEq ps (tys (paramsLayout fd.params)), decEq cv (Linkage.ConvertsIn.convertsIn fd.name)) of
        (Yes Refl, Yes Refl, Yes Refl) => Just (fd.name, MkCallee fd (n ** var))
        _ => Nothing
    one _ = Nothing

------------------------------------------------------------------------------
-- Primitive types and operations

||| The word of an integer or character constant, extended as its type is.
constWord : Constant -> Maybe Int64
constWord (I n) = Just (cast n)
constWord (I8 n) = Just (cast n)
constWord (I16 n) = Just (cast n)
constWord (I32 n) = Just (cast n)
constWord (I64 n) = Just n
constWord (B8 n) = Just (cast n)
constWord (B16 n) = Just (cast n)
constWord (B32 n) = Just (cast n)
constWord (B64 n) = let i : Integer = cast n in
                    Just (cast (if i >= 9223372036854775808 then i - 18446744073709551616 else i))
constWord (Ch c) = Just (cast (ord c))
constWord _ = Nothing

||| How a machine integer type is held in a word: narrower than it, extended
||| from the width as the type is signed or not, or the whole word.
data Held = Narrower IRCommon.Op.SubWord Bool | Whole Bool

------------------------------------------------------------------------------
-- The lowering

||| What the lowering of a form knows of the program: the forms it may call,
||| the shapes of the data types, the OS services' externs, each bound to the
||| function that implements it on the platform, the inline externs, each
||| with the intrinsic it is, and the backend's primitives, each with the
||| primitive it is.
public export
record Forms (enc : Types.Enc) (d : TermIR.Decls enc) where
  constructor MkForms
  callees : SortedMap Name (Callee d)
  shapes : Flat.Exp.Shapes
  services : SortedMap Name Name
  externs : SortedMap Name Intrinsic
  primitives : SortedMap Name Primitive

||| Each variable in scope: its type's skeleton and its value.
Env : (enc : Types.Enc) -> (IRCommon.Ty enc -> Type) -> Type
Env enc v = SortedMap Name (Flat.Exp.Skeleton, Value enc v)

parameters {enc : Types.Enc} (0 d : TermIR.Decls enc) (pr : Forms enc d) (self : Flat.Exp.FlatDef) (m : Bool)
           {0 v : IRCommon.Ty enc -> Type} {0 l : List (IRCommon.Ty enc) -> Type}

  0 B : Type -> Type
  B = TermIR.Build d (IRCommon.Conv.Direct (tys self.result) False) m v l

  0 E : Type
  E = TermIR.Build.End d (IRCommon.Conv.Direct (tys self.result) False) m v l

  0 Again : Type
  Again = TermIR.Build.Jumper d (IRCommon.Conv.Direct (tys self.result) False) m v l (tys (paramsLayout self.params))

  ------------------------------------------------------------------------------
  -- Words and doubles

  word : Value enc v -> B (TermIR.Opnd v IRCommon.Ty.W64)
  word x = maybe (TermIR.Build.unsupported "a word of another layout") pure (wordOf x)

  ------------------------------------------------------------------------------
  -- Expressions

  ||| The variables of an alternative, bound to the registers of the fields.
  bindFields : Env enc v -> List Flat.Exp.FlatVar -> Value enc v -> Maybe (Env enc v)
  bindFields env [] (MkValue [] []) = Just env
  bindFields env [] _ = Nothing
  bindFields env (fv :: fvs) val = do
    (xs, rest) <- takeRegs fv.layout val
    bindFields (insert fv.name (fv.skeleton, MkValue fv.layout xs) env) fvs rest

  mutual
    ||| An expression's value, and its type's skeleton.
    expr : Env enc v -> Flat.Exp -> B (Flat.Exp.Skeleton, Value enc v)
    expr env exp = case exp of
      Flat.Exp.FVar _ x => case lookup x env of
                 Just t => pure t
                 Nothing => TermIR.Build.unsupported ("the unbound variable " ++ show x ++ " in a flat form")
      Flat.Exp.FLet _ fv val sc => do
                 env' <- bind env fv val
                 expr env' sc
      Flat.Exp.FConst _ k => constant k
      Flat.Exp.FOp _ op args => do
        xs <- traverse (\a => snd <$> expr env a) args
        primOp op xs
      Flat.Exp.FCall _ n args => do
                 xs <- traverse (\a => snd <$> expr env a) args
                 callForm n xs
      Flat.Exp.FPrim _ n sk lay args => case lookup n pr.externs of
                 Nothing => case lookup n pr.services of
                   -- an OS service: a call of the platform's function for it
                   Just f => do
                     xs <- traverse (\a => snd <$> expr env a) args
                     (_, x) <- callForm f xs
                     maybe
                       (TermIR.Build.unsupported ("the OS service " ++ show n ++ ", whose result is not its type's"))
                           (\rs => pure (sk, MkValue lay rs)) (regsAs lay x)
                   Nothing => case lookup n pr.primitives of
                     -- one of the backend's: its instructions
                     Just p => do
                       xs <- traverse (\a => snd <$> expr env a) args
                       x <- primitive n p (concatValues xs)
                       maybe
                         (TermIR.Build.unsupported ("the primitive " ++ show n ++ ", whose result is not its type's"))
                             (\rs => pure (sk, MkValue lay rs)) (regsAs lay x)
                     Nothing => TermIR.Build.unsupported ("the primitive " ++ show n ++ " in a flat form")
                 Just i => do
                   xs <- traverse (\a => snd <$> expr env a) args
                   x <- inlineExtern n i (concatValues xs)
                   maybe
                     (TermIR.Build.unsupported ("the inline extern " ++ show n ++ ", whose result is not its type's"))
                         (\rs => pure (sk, MkValue lay rs)) (regsAs lay x)
      Flat.Exp.FCon _ c _ sk lay args => do
                 xs <- traverse (\a => snd <$> expr env a) args
                 x <- construct sk c (concatValues xs)
                 case regsAs lay x of
                   Just rs => pure (sk, MkValue lay rs)
                   Nothing =>
                     TermIR.Build.unsupported ("the constructor " ++ show c ++ ", whose layout is not its type's")
      e@(Flat.Exp.FCase _ scr alts def) => case typeOf (layouts env) e of
        Nothing => do
          _ <- TermIR.Build.joinPoint [] $ \exit => dispatch env scr alts def (\env', b => do _ <- expr env' b; exit [])
          TermIR.Build.unsupported "a case that has no value"
        Just (sk, lay) => do
          rs <- TermIR.Build.joinPoint (tys lay) $ \exit =>
            dispatch env scr alts def $ \env', b => do
              (_, x) <- expr env' b
              maybe (TermIR.Build.unsupported "an alternative of another layout") exit (regsAs lay x)
          pure (sk, MkValue lay rs)
      Flat.Exp.FCrash _ msg => TermIR.Build.crash msg
      Flat.Exp.FNone _ => pure (Flat.Exp.SOther, noRegs)
      where
        ||| A value of the primitive type.
        prim : PrimType -> Value enc v -> (Flat.Exp.Skeleton, Value enc v)
        prim t x = (Flat.Exp.SPrim t, x)

        wordVal : PrimType -> TermIR.Opnd v IRCommon.Ty.W64 -> (Flat.Exp.Skeleton, Value enc v)
        wordVal t w = prim t (MkValue [Flat.Exp.Word] [w])

        doubleVal : TermIR.Opnd v IRCommon.Ty.F64 -> (Flat.Exp.Skeleton, Value enc v)
        doubleVal f = prim DoubleType (MkValue [Flat.Exp.Dbl] [f])

        constant : Constant -> B (Flat.Exp.Skeleton, Value enc v)
        constant (Db x) = doubleVal <$> TermIR.Build.emit1 (TermIR.Instr.FConst x)
        constant WorldVal = pure (Flat.Exp.SPrim WorldType, noRegs)
        constant k = case (Flat.ConstType.constType k, constWord k) of
          (Just t, Just w) => pure (wordVal t (TermIR.Opnd.W w))
          _ => TermIR.Build.unsupported ("the constant " ++ show k ++ " in a flat form")

        ||| A primitive's instructions, from its arguments' registers, which are
        ||| its signature's, into its results'.
        primitive : Name -> Primitive -> Value enc v -> B (Value enc v)
        primitive n Primitive.Mul128 (MkValue [Flat.Exp.Word, Flat.Exp.Word] [x, y]) = do
          [h, l] <- TermIR.Build.emit (TermIR.Instr.Mul128 x y)
          pure (MkValue [Flat.Exp.Word, Flat.Exp.Word] [TermIR.Opnd.V h, TermIR.Opnd.V l])
        primitive n _ _ = TermIR.Build.unsupported ("the primitive " ++ show n ++ " on registers other than its signature's")

        ||| An inline extern's instructions, from its arguments' registers, which
        ||| are its port's: the intrinsic's expansion (`Linkage.Expansion`), which
        ||| Idris has checked against the same port.
        inlineExtern : Name -> Intrinsic -> Value enc v -> B (Value enc v)
        inlineExtern n i x = case operands (Linkage.Routine.portParams (Intrinsic.port i)) x.layout x.regs of
          Just os => expand (Linkage.Expansion.expansion i) os
          Nothing => TermIR.Build.unsupported ("the inline extern " ++ show n ++ " on registers other than its port's")
          where
            outside : B a
            outside = TermIR.Build.unsupported ("the inline extern " ++ show n ++ " outside the memory module")

            -- the registers of a value, as the types its port gives them
            operands : (ts : List (IRCommon.Ty enc)) -> (l : Flat.Exp.Layout) -> All (TermIR.Opnd v) (tys l) ->
                       Maybe (All (TermIR.Opnd v) ts)
            operands [] [] [] = Just []
            operands (IRCommon.Ty.W64 :: ts) (Flat.Exp.Word :: l) (r :: rs) = (r ::) <$> operands ts l rs
            operands (IRCommon.Ty.Val :: ts) (Flat.Exp.Uniform :: l) (r :: rs) = (r ::) <$> operands ts l rs
            operands _ _ _ = Nothing

            word : TermIR.Opnd v IRCommon.Ty.W64 -> Value enc v
            word w = MkValue [Flat.Exp.Word] [w]

            -- a pinned register as a word, and set from one: the continuation is
            -- a pointer, converted from or to its word, so that only this
            -- module's functions read or set it
            getWord : IRCommon.Pinned -> B (TermIR.Opnd v IRCommon.Ty.W64)
            getWord IRCommon.Pinned.Hp = TermIR.Build.emit1 (TermIR.Instr.GetPinned IRCommon.Pinned.Hp)
            getWord IRCommon.Pinned.HpLim = TermIR.Build.emit1 (TermIR.Instr.GetPinned IRCommon.Pinned.HpLim)
            getWord IRCommon.Pinned.K = case m of
              True => do
                p <- TermIR.Build.emit1 (TermIR.Instr.GetPinned IRCommon.Pinned.K)
                TermIR.Build.emit1 (TermIR.Instr.AddrToWord p)
              False => outside

            setWord : IRCommon.Pinned -> TermIR.Opnd v IRCommon.Ty.W64 -> B ()
            setWord IRCommon.Pinned.Hp x = TermIR.Build.emit0 (TermIR.Instr.SetPinned IRCommon.Pinned.Hp x)
            setWord IRCommon.Pinned.HpLim x = TermIR.Build.emit0 (TermIR.Instr.SetPinned IRCommon.Pinned.HpLim x)
            setWord IRCommon.Pinned.K x = case m of
              True => do
                p <- TermIR.Build.emit1 (TermIR.Instr.WordToAddr Types.Kind.CONT x)
                TermIR.Build.emit0 (TermIR.Instr.SetPinned IRCommon.Pinned.K p)
              False => outside

            -- the instructions an expansion stands for, on its port's operands
            expand : Linkage.Expansion p -> All (TermIR.Opnd v) (Linkage.Routine.portParams {enc} p) ->
                    B (Value enc v)
            expand (Linkage.Expansion.Load Linkage.Expansion.Whole) [base, off] = do
              a <- TermIR.Build.emit1 (TermIR.Instr.Arith Add base off)
              word <$> TermIR.Build.emit1 (TermIR.Instr.Load IRCommon.Ty.W64 (TermIR.MkMem (TermIR.Mem.AtWord a) Nothing 0))
            expand (Linkage.Expansion.Load (Linkage.Expansion.Narrow sw)) [base, off] = do
              a <- TermIR.Build.emit1 (TermIR.Instr.Arith Add base off)
              word <$> TermIR.Build.emit1 (TermIR.Instr.LoadN sw False (TermIR.MkMem (TermIR.Mem.AtWord a) Nothing 0))
            expand (Linkage.Expansion.Store Linkage.Expansion.Whole) [base, off, x] = do
              a <- TermIR.Build.emit1 (TermIR.Instr.Arith Add base off)
              TermIR.Build.emit0 (TermIR.Instr.Store IRCommon.Ty.W64 (TermIR.MkMem (TermIR.Mem.AtWord a) Nothing 0) x)
              pure noRegs
            expand (Linkage.Expansion.Store (Linkage.Expansion.Narrow sw)) [base, off, x] = do
              a <- TermIR.Build.emit1 (TermIR.Instr.Arith Add base off)
              TermIR.Build.emit0 (TermIR.Instr.StoreN sw (TermIR.MkMem (TermIR.Mem.AtWord a) Nothing 0) x)
              pure noRegs
            expand (Linkage.Expansion.Get r) [] = word <$> getWord r
            expand (Linkage.Expansion.Set IRCommon.Pinned.Hp) [x] = do setWord IRCommon.Pinned.Hp x; pure noRegs
            expand (Linkage.Expansion.Set IRCommon.Pinned.HpLim) [x] = do setWord IRCommon.Pinned.HpLim x; pure noRegs
            expand (Linkage.Expansion.Set IRCommon.Pinned.K) [x] = do setWord IRCommon.Pinned.K x; pure noRegs
            expand Linkage.Expansion.PointerTag [] = pure (word (TermIR.Opnd.W (cast (HeapObj.ValEnc.pointerTag enc.val))))
            expand (Linkage.Expansion.AreaAddress a) [] = word <$> TermIR.Build.emit1 (TermIR.Instr.AreaAddr a)
            -- a uniform value and a word: the conversions, so this module's
            -- functions alone
            expand Linkage.Expansion.ValueWord [u] = case m of
              True => word <$> TermIR.Build.emit1 (TermIR.Instr.ValToWord u)
              False => outside
            expand Linkage.Expansion.WordValue [w] = case m of
              True => do
                u <- TermIR.Build.emit1 (TermIR.Instr.WordToVal w)
                pure (MkValue [Flat.Exp.Uniform] [u])
              False => outside
            expand Linkage.Expansion.Syscall [a0, a1, a2, a3, a4, a5, a6] =
              word <$> TermIR.Build.emit1 (TermIR.Instr.SystemCall 6 [a0, a1, a2, a3, a4, a5, a6])

        ||| A constructor's value, from its fields'.
        construct : Flat.Exp.Skeleton -> Name -> Value enc v -> B (Value enc v)
        construct sk c fs = case Flat.Exp.shapeOf pr.shapes sk of
          Just (Flat.Exp.DataShape cs) => case placement cs c of
            Just (_, p) => conValue p fs
            Nothing => TermIR.Build.unsupported ("the constructor " ++ show c ++ ", which is not one of " ++ show sk)
          _ => TermIR.Build.unsupported ("a constructor of " ++ show sk ++ ", whose shape is not known")

        ||| The skeleton and layout of an expression's value, from the variables'
        ||| and the callees' results.
        typeOf : SortedMap Name (Flat.Exp.Skeleton, Flat.Exp.Layout) -> Flat.Exp ->
                 Maybe (Flat.Exp.Skeleton, Flat.Exp.Layout)
        typeOf env = Flat.Exp.expType (\x => lookup x env)
                             (\n => (\c => (c.form.resultSkeleton, c.form.result)) <$> lookup n pr.callees)

        layouts : Env enc v -> SortedMap Name (Flat.Exp.Skeleton, Flat.Exp.Layout)
        layouts = map (\(sk, x) => (sk, x.layout))

        ||| A primitive operation.
        primOp : PrimFn n -> Vect n (Value enc v) -> B (Flat.Exp.Skeleton, Value enc v)
        primOp fn vect = case (fn, vect) of
          (Add t, [x, y]) => arith t Add IRCommon.Op.FAdd x y
          (Sub t, [x, y]) => arith t Sub IRCommon.Op.FSub x y
          (Mul t, [x, y]) => arith t Mul IRCommon.Op.FMul x y
          (Div DoubleType, [x, y]) => do a <- double x
                                         b <- double y
                                         doubleVal <$> TermIR.Build.emit1 (TermIR.Instr.FArith IRCommon.Op.FDiv a b)
          (Div t, [x, y]) => withHeld t "division" $ \h => do
            a <- word x
            b <- word y
            Words.nonZero b
            w <- Words.divide (signed h) False a b
            wordVal t <$> wrap h w
          (Mod t, [x, y]) => withHeld t "remainder" $ \h => do
            a <- word x
            b <- word y
            Words.nonZero b
            w <- Words.divide (signed h) True a b
            wordVal t <$> wrap h w
          (Neg DoubleType, [x]) => do a <- double x; doubleVal <$> TermIR.Build.emit1 (TermIR.Instr.FNeg a)
          (Neg t, [x]) => withHeld t "negation" $ \h => do
            a <- word x
            w <- TermIR.Build.emit1 (TermIR.Instr.Unary IRCommon.Op.Negate a)
            wordVal t <$> wrap h w
          (ShiftL t, [x, y]) => shifting t True x y
          (ShiftR t, [x, y]) => shifting t False x y
          (BAnd t, [x, y]) => bitwise t IRCommon.Op.And x y
          (BOr t, [x, y]) => bitwise t IRCommon.Op.Or x y
          (BXOr t, [x, y]) => bitwise t IRCommon.Op.Xor x y
          (LT t, [x, y]) => comparison t IRCommon.Op.LtS x y
          (LTE t, [x, y]) => comparison t IRCommon.Op.LeS x y
          (EQ t, [x, y]) => comparison t IRCommon.Op.EqR x y
          (GTE t, [x, y]) => comparison t IRCommon.Op.GeS x y
          (GT t, [x, y]) => comparison t IRCommon.Op.GtS x y
          (Cast from to, [x]) => castTo from to x
          (op, _) => TermIR.Build.unsupported ("the primitive " ++ show op ++ " in a flat form")
          where
            ||| A word wrapped to the type's width, extended again.
            wrap : Held -> TermIR.Opnd v IRCommon.Ty.W64 -> B (TermIR.Opnd v IRCommon.Ty.W64)
            wrap (Narrower sw s) w = TermIR.Build.emit1 (TermIR.Instr.Ext sw s w)
            wrap (Whole _) w = pure w

            double : Value enc v -> B (TermIR.Opnd v IRCommon.Ty.F64)
            double x = maybe (TermIR.Build.unsupported "a double of another layout") pure (doubleOf x)

            withHeld : PrimType -> String -> (Held -> B a) -> B a
            withHeld t what k = case held t of
              Just h => k h
              Nothing => TermIR.Build.unsupported (what ++ " on " ++ show t ++ " in a flat form")
              where
                ||| How an integer type or `Char` is held; `Char` as its code point.
                held : PrimType -> Maybe Held
                held IntType = Just (Whole True)
                held Int64Type = Just (Whole True)
                held Bits64Type = Just (Whole False)
                held Int8Type = Just (Narrower IRCommon.Op.Sub8 True)
                held Int16Type = Just (Narrower IRCommon.Op.Sub16 True)
                held Int32Type = Just (Narrower IRCommon.Op.Sub32 True)
                held Bits8Type = Just (Narrower IRCommon.Op.Sub8 False)
                held Bits16Type = Just (Narrower IRCommon.Op.Sub16 False)
                held Bits32Type = Just (Narrower IRCommon.Op.Sub32 False)
                held CharType = Just (Narrower IRCommon.Op.Sub32 False)
                held _ = Nothing

            ||| A cast between the primitive types.
            castTo : PrimType -> PrimType -> Value enc v -> B (Flat.Exp.Skeleton, Value enc v)
            castTo from to x =
              if from == to then pure (prim to x) else
              case (from, to) of
                (DoubleType, CharType) => do f <- double x; w <- doubleToWord (Whole True) f; wordVal to <$> toChar w
                (DoubleType, _) => withHeld to "a cast" $ \h => do f <- double x; wordVal to <$> doubleToWord h f
                (_, DoubleType) => withHeld from "a cast" $ \h => do w <- word x; doubleVal <$> wordToDouble h w
                (_, CharType) => withHeld from "a cast" $ \_ => do w <- word x; wordVal to <$> toChar w
                _ => withHeld from "a cast" $ \_ => withHeld to "a cast" $ \h => do
                       w <- word x
                       wordVal to <$> wrap h w
              where
                ||| A word as a `Char`: itself if it is a Unicode scalar value, 0 if not.
                toChar : TermIR.Opnd v IRCommon.Ty.W64 -> B (TermIR.Opnd v IRCommon.Ty.W64)
                toChar w = do
                  [r] <- TermIR.Build.joinPoint [IRCommon.Ty.W64] $ \done => do
                    keep <- TermIR.Build.block [] $ \[] => done [w]
                    zero <- TermIR.Build.block [] $ \[] => done [TermIR.Opnd.W 0]
                    TermIR.Build.branch IRCommon.Op.LtS w (TermIR.Opnd.W 0) (zero []) $
                      TermIR.Build.branch IRCommon.Op.LeS w (TermIR.Opnd.W 55295) (keep []) $
                        TermIR.Build.branch IRCommon.Op.LtS w (TermIR.Opnd.W 57344) (zero []) $
                          TermIR.Build.branch IRCommon.Op.LeS w (TermIR.Opnd.W 1114111) (keep []) (zero [])
                  pure r

                ||| A word of the integer type as a double. A `Bits64` at or above 2^63
                ||| is halved, its low bit kept for the rounding, converted and doubled.
                wordToDouble : Held -> TermIR.Opnd v IRCommon.Ty.W64 -> B (TermIR.Opnd v IRCommon.Ty.F64)
                wordToDouble (Whole False) w = do
                  [f] <- TermIR.Build.joinPoint [IRCommon.Ty.F64] $ \done =>
                    TermIR.Build.branch IRCommon.Op.GeS w (TermIR.Opnd.W 0)
                      (do f <- TermIR.Build.emit1 (TermIR.Instr.Convert IRCommon.Op.I2F w); done [f]) $ do
                      h <- TermIR.Build.emit1 (TermIR.Instr.Arith IRCommon.Op.Shr w (TermIR.Opnd.W 1))
                      b <- TermIR.Build.emit1 (TermIR.Instr.Arith IRCommon.Op.And w (TermIR.Opnd.W 1))
                      hb <- TermIR.Build.emit1 (TermIR.Instr.Arith IRCommon.Op.Or h b)
                      f <- TermIR.Build.emit1 (TermIR.Instr.Convert IRCommon.Op.I2F hb)
                      f2 <- TermIR.Build.emit1 (TermIR.Instr.FArith IRCommon.Op.FAdd f f)
                      done [f2]
                  pure f
                wordToDouble _ w = TermIR.Build.emit1 (TermIR.Instr.Convert IRCommon.Op.I2F w)

                ||| A double truncated to the integer type. A `Bits64` at or above 2^63 is
                ||| converted less 2^63, which is added back to the word.
                doubleToWord : Held -> TermIR.Opnd v IRCommon.Ty.F64 -> B (TermIR.Opnd v IRCommon.Ty.W64)
                doubleToWord (Whole False) f = do
                  big <- TermIR.Build.emit1 (TermIR.Instr.FConst 9223372036854775808.0)
                  above <- TermIR.Build.emit1 (TermIR.Instr.FCmp IRCommon.Op.GeS f big)
                  [w] <- TermIR.Build.joinPoint [IRCommon.Ty.W64] $ \done =>
                    TermIR.Build.branch IRCommon.Op.EqR above (TermIR.Opnd.W 0)
                      (do w <- TermIR.Build.emit1 (TermIR.Instr.Convert IRCommon.Op.F2I f); done [w]) $ do
                      g <- TermIR.Build.emit1 (TermIR.Instr.FArith IRCommon.Op.FSub f big)
                      w <- TermIR.Build.emit1 (TermIR.Instr.Convert IRCommon.Op.F2I g)
                      w' <- TermIR.Build.emit1 (TermIR.Instr.Arith Add w (TermIR.Opnd.W (-9223372036854775808)))
                      done [w']
                  pure w
                doubleToWord h f = do
                  w <- TermIR.Build.emit1 (TermIR.Instr.Convert IRCommon.Op.F2I f)
                  wrap h w

            arith : PrimType -> IRCommon.Op.ArithOp -> IRCommon.Op.FOp -> (x, y : Value enc v) ->
                    B (Flat.Exp.Skeleton, Value enc v)
            arith DoubleType _ o x y = do a <- double x
                                          b <- double y
                                          doubleVal <$> TermIR.Build.emit1 (TermIR.Instr.FArith o a b)
            arith t o _ x y = withHeld t "arithmetic" $ \h => do
              a <- word x
              b <- word y
              w <- TermIR.Build.emit1 (TermIR.Instr.Arith o a b)
              wordVal t <$> wrap h w

            bitwise : PrimType -> IRCommon.Op.ArithOp -> (x, y : Value enc v) -> B (Flat.Exp.Skeleton, Value enc v)
            bitwise t o x y = withHeld t "a bitwise operation" $ \h => do
              a <- word x
              b <- word y
              w <- TermIR.Build.emit1 (TermIR.Instr.Arith o a b)
              wordVal t <$> wrap h w

            signed : Held -> Bool
            signed (Narrower _ s) = s
            signed (Whole s) = s

            shifting : PrimType -> (left : Bool) -> (x, y : Value enc v) -> B (Flat.Exp.Skeleton, Value enc v)
            shifting t left x y = withHeld t "a shift" $ \h => do
              a <- word x
              k <- word y
              w <- Words.shiftBy
                (if left then IRCommon.Op.Shl else if signed h then IRCommon.Op.Sar else IRCommon.Op.Shr) a k
              wordVal t <$> wrap h w

            comparison : PrimType -> IRCommon.Op.Rel -> (x, y : Value enc v) -> B (Flat.Exp.Skeleton, Value enc v)
            comparison DoubleType rel x y = do
              a <- double x
              b <- double y
              wordVal IntType <$> TermIR.Build.emit1 (TermIR.Instr.FCmp rel a b)
            comparison t rel x y = withHeld t "a comparison" $ \h => do
              a <- word x
              b <- word y
              wordVal IntType <$> TermIR.Build.emit1 (TermIR.Instr.Cmp (if signed h then rel else unsignedRel rel) a b)
              where
                ||| The unsigned relation for a signed one.
                unsignedRel : IRCommon.Op.Rel -> IRCommon.Op.Rel
                unsignedRel IRCommon.Op.LtS = IRCommon.Op.LtU
                unsignedRel IRCommon.Op.LeS = IRCommon.Op.LeU
                unsignedRel IRCommon.Op.GtS = IRCommon.Op.GtU
                unsignedRel IRCommon.Op.GeS = IRCommon.Op.GeU
                unsignedRel r = r

        ||| A call of a form.
        callForm : Name -> List (Value enc v) -> B (Flat.Exp.Skeleton, Value enc v)
        callForm n xs = case lookup n pr.callees of
          Nothing => TermIR.Build.unsupported ("a call of " ++ show n ++ ", which has no flat form in the program")
          Just (MkCallee fd (_ ** var)) => case regsAs (paramsLayout fd.params) (concatValues xs) of
            Nothing => TermIR.Build.unsupported ("a call of " ++ show n ++ " with arguments of other layouts")
            Just args => do
              rs <- TermIR.Build.directCall var args
              pure (fd.resultSkeleton, MkValue fd.result rs)

    ||| A `let`: the variable bound to the value.
    bind : Env enc v -> Flat.Exp.FlatVar -> Flat.Exp -> B (Env enc v)
    bind env fv val = do
      (_, x) <- expr env val
      case regsAs fv.layout x of
        Just rs => pure (insert fv.name (fv.skeleton, MkValue fv.layout rs) env)
        Nothing => TermIR.Build.unsupported ("the value of " ++ show fv.name ++ ", whose layout is not its type's")

    ||| A case: the scrutinee, then each alternative's body as `k` lowers it,
    ||| in the environment of its variables.
    dispatch : Env enc v -> Flat.Exp -> List Flat.Exp.FlatAlt -> Maybe Flat.Exp -> (Env enc v -> Flat.Exp -> E) -> E
    dispatch env scr alts def k = do
      (sk, x) <- expr env scr
      let other = maybe (TermIR.Build.crash "no case alternative matched") (k env) def
      case alts of
        [] => other
        Flat.Exp.FConstAlt _ _ :: _ => constCase env x alts other k
        Flat.Exp.FConAlt _ _ _ _ :: _ => conCase env sk x alts other k
      where
        constCase : Env enc v -> Value enc v -> List Flat.Exp.FlatAlt -> E -> (Env enc v -> Flat.Exp -> E) -> E
        constCase env x alts other k = do
          w <- word x
          let cs = mapMaybe (\a => case a of
                                     Flat.Exp.FConstAlt c b => (\i => (i, k env b)) <$> constWord c
                                     _ => Nothing) alts
          if length cs /= length alts then TermIR.Build.unsupported "a case on constants that are not words" else
            case choose
              (Data.Distinct.distinct (map fst cs) && TermIR.Body.keysFit (IRCommon.Ty.W64 {enc}) (map fst cs)) of
              Left ok => TermIR.Build.switch w cs other
              Right _ => TermIR.Build.unsupported "a case with repeated constants"

        conCase : Env enc v -> Flat.Exp.Skeleton -> Value enc v -> List Flat.Exp.FlatAlt -> E ->
                  (Env enc v -> Flat.Exp -> E) -> E
        conCase env sk x alts other k = case Flat.Exp.shapeOf pr.shapes sk of
          Just (Flat.Exp.DataShape [c]) => case find (named c.name) alts of
            Just (Flat.Exp.FConAlt _ _ vs b) =>
              alternative env (MkPlacement Nothing [] (Flat.Exp.fieldsLayout c.fields) []) x vs b k
            _ => other
          Just (Flat.Exp.DataShape cs) => do
            t <- maybe (TermIR.Build.unsupported "a sum without its tag") pure (tagOf x)
            let branches = mapMaybe (\a => case a of
                                             Flat.Exp.FConAlt cn _ vs b => do
                                                        (c, p) <- placement cs cn
                                                        pure (the Int64 (cast c.tag), alternative env p x vs b k)
                                             _ => Nothing) alts
            if length branches /= length alts
              then TermIR.Build.unsupported ("a case on a constructor that is not one of " ++ show sk) else
              case choose
                (Data.Distinct.distinct (map fst branches)
                 && TermIR.Body.keysFit (IRCommon.Ty.W64 {enc}) (map fst branches)) of
                Left ok => TermIR.Build.switch t branches other
                Right _ => TermIR.Build.unsupported "a case with repeated constructors"
          _ => TermIR.Build.unsupported ("a case on " ++ show sk ++ ", whose shape is not known")
          where
            named : Name -> Flat.Exp.FlatAlt -> Bool
            named n (Flat.Exp.FConAlt cn _ _ _) = cn == n
            named _ _ = False

            alternative : Env enc v -> Placement -> Value enc v -> List Flat.Exp.FlatVar -> Flat.Exp ->
                          (Env enc v -> Flat.Exp -> E) -> E
            alternative env p x vs b k = case fieldsOf p x >>= bindFields env vs of
              Just env' => k env' b
              Nothing => TermIR.Build.unsupported "an alternative whose fields are not its constructor's"

  ||| The form's body, from the parameters' registers.
  formBody : Maybe Again -> All (TermIR.Opnd v) (tys (paramsLayout self.params)) -> E
  formBody again xs = case bindFields empty self.params (MkValue (paramsLayout self.params) xs) of
    Just env => tailExp env again self.body
    Nothing => TermIR.Build.unsupported "parameters whose layouts are not their types'"
    where
      ||| An expression in tail position: its value is the result, and a call of
      ||| the form itself jumps back to its start.
      tailExp : Env enc v -> Maybe Again -> Flat.Exp -> E
      tailExp env x exp = case (x, exp) of
        (again, Flat.Exp.FLet _ fv val sc) => do
          env' <- bind env fv val
          tailExp env' again sc
        (again, Flat.Exp.FCase _ scr alts def) => dispatch env scr alts def (\env', b => tailExp env' again b)
        (Just again, e@(Flat.Exp.FCall _ n args)) =>
          if n /= self.name then returned env e else do
            xs <- traverse (\a => snd <$> expr env a) args
            maybe (TermIR.Build.unsupported "a call of the form itself with arguments of other layouts") again
                  (regsAs (paramsLayout self.params) (concatValues xs))
        (_, Flat.Exp.FCrash _ msg) => TermIR.Build.crash msg
        (_, e) => returned env e
        where
          ||| The expression's value, returned.
          returned : Env enc v -> Flat.Exp -> E
          returned env e = do
            (_, x) <- expr env e
            maybe (TermIR.Build.unsupported "a result whose layout is not the form's") TermIR.Build.ret
              (regsAs self.result x)

||| A form as the body of its `Direct` function. A form that calls itself
||| is a loop, which a call in tail position jumps back to.
export
lowerForm : {enc : Types.Enc} -> (0 d : TermIR.Decls enc) -> Forms enc d -> (fd : Flat.Exp.FlatDef) ->
            TermIR.Build.Closed d (IRCommon.Conv.Direct (tys fd.result) False) (Linkage.ConvertsIn.convertsIn fd.name)
              (tys (paramsLayout fd.params))
lowerForm d pr fd = TermIR.Build.build $ \xs =>
  if calls fd.name fd.body
     then TermIR.Build.loop (tys (paramsLayout fd.params)) xs $ \again,
       ys => formBody d pr fd (Linkage.ConvertsIn.convertsIn fd.name) (Just again) ys
     else formBody d pr fd (Linkage.ConvertsIn.convertsIn fd.name) Nothing xs
  where
    ||| Whether the expression calls the form.
    calls : Name -> Flat.Exp -> Bool
    calls n (Flat.Exp.FVar _ _) = False
    calls n (Flat.Exp.FLet _ _ val sc) = calls n val || calls n sc
    calls n (Flat.Exp.FConst _ _) = False
    calls n (Flat.Exp.FOp _ _ as) = any (calls n) (toList as)
    calls n (Flat.Exp.FCall _ f as) = f == n || any (calls n) as
    calls n (Flat.Exp.FPrim _ _ _ _ as) = any (calls n) as
    calls n (Flat.Exp.FCon _ _ _ _ _ as) = any (calls n) as
    calls n (Flat.Exp.FCase _ sc alts def) = calls n sc || any alt alts || maybe False (calls n) def
      where
        alt : Flat.Exp.FlatAlt -> Bool
        alt (Flat.Exp.FConAlt _ _ _ b) = calls n b
        alt (Flat.Exp.FConstAlt _ b) = calls n b
    calls n (Flat.Exp.FCrash _ _) = False
    calls n (Flat.Exp.FNone _) = False
