||| The flat lowering: a flat form (`Flat.Exp`) to a `Direct` function of
||| the term IR (`Compiler.Native.TermIR`), written in `Build`.
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
||| lowering is the same under every encoding but for the intrinsic that
||| names the encoding's pointer tag. The functions of the module that
||| implements the runtime's memory may convert between words and addresses
||| (`convertsIn`), which the intrinsics on the current continuation need; no
||| other may. A `case` on a sum is a switch on the tag, and one that is not
||| in tail position a join, whose parameters are the case's registers. A
||| call of a form is a `DirectCall`; a call of the form itself in tail
||| position jumps back to its start, so self tail recursion is a loop. The
||| runtime's intrinsics (`Compiler.Native.Linkage.intrinsics`) lower to the
||| instructions they stand for, and its OS services to calls of the
||| functions that implement them on the platform; every other `%extern` and `%foreign` primitive (`FPrim`), the
||| operations on strings and the double functions of the C library lower to
||| `Unsupported`.
module Compiler.Native.LowerFlat

import public Compiler.Native.Linkage

import Compiler.Native.Words
import Core.Name
import Core.TT
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.Vect
import Decidable.Equality
import Flat.Exp

%default covering

------------------------------------------------------------------------------
-- Registers

export
DecEq Rep where
  decEq Word Word = Yes Refl
  decEq Dbl Dbl = Yes Refl
  decEq Uniform Uniform = Yes Refl
  decEq Word Dbl = No (\case Refl impossible)
  decEq Word Uniform = No (\case Refl impossible)
  decEq Dbl Word = No (\case Refl impossible)
  decEq Dbl Uniform = No (\case Refl impossible)
  decEq Uniform Word = No (\case Refl impossible)
  decEq Uniform Dbl = No (\case Refl impossible)

||| The type of a register of the representation.
public export
repTy : Rep -> Ty enc
repTy Word = W64
repTy Dbl = F64
repTy Uniform = Val

||| The types of a layout's registers.
public export
tys : Layout -> List (Ty enc)
tys [] = []
tys (r :: rs) = repTy r :: tys rs

||| The registers of a form's parameters, in turn.
public export
paramsLayout : List FlatVar -> Layout
paramsLayout [] = []
paramsLayout (p :: ps) = p.layout ++ paramsLayout ps

||| The signature of a form's `Direct` function.
export
formSig : FlatDef -> Sig enc
formSig fd = MkSig (flatName fd.name) (InDirect (tys fd.result) False) (tys (paramsLayout fd.params)) (convertsIn fd.name)

------------------------------------------------------------------------------
-- Values

||| A flat value: its layout and its registers.
public export
record Value (enc : Enc) (v : Ty enc -> Type) where
  constructor MkValue
  layout : Layout
  regs : All (Opnd v) (tys layout)

||| The value of no registers.
export
noRegs : Value enc v
noRegs = MkValue [] []

||| The registers of one value, then of the other.
export
appendValues : Value enc v -> Value enc v -> Value enc v
appendValues (MkValue a xs) (MkValue b ys) = MkValue (a ++ b) (go a xs)
  where
    go : (a' : Layout) -> All (Opnd v) (tys a') -> All (Opnd v) (tys (a' ++ b))
    go [] [] = ys
    go (_ :: rs) (x :: xs') = x :: go rs xs'

export
concatValues : List (Value enc v) -> Value enc v
concatValues = foldr appendValues noRegs

||| A value's first registers, of the layout, and the rest; nothing if it does
||| not start with them.
export
takeRegs : (a : Layout) -> Value enc v -> Maybe (All (Opnd v) (tys a), Value enc v)
takeRegs [] val = Just ([], val)
takeRegs (r :: rs) (MkValue (r' :: ls) (x :: xs)) = case decEq r r' of
  Yes Refl => do (ys, rest) <- takeRegs rs (MkValue ls xs)
                 Just (x :: ys, rest)
  No _ => Nothing
takeRegs _ _ = Nothing

||| A value's registers as those of the layout, if they are.
export
regsAs : (a : Layout) -> Value enc v -> Maybe (All (Opnd v) (tys a))
regsAs a val = case takeRegs a val of
  Just (xs, MkValue [] []) => Just xs
  _ => Nothing

||| A value cut into values of the layouts, in turn, if it is made of them.
export
splitBy : List Layout -> Value enc v -> Maybe (List (Value enc v))
splitBy [] (MkValue [] []) = Just []
splitBy [] _ = Nothing
splitBy (a :: as) val = do
  (xs, rest) <- takeRegs a val
  (MkValue a xs ::) <$> splitBy as rest

||| The tag of a sum's value: its first register.
export
tagOf : Value enc v -> Maybe (Opnd v W64)
tagOf (MkValue (Word :: _) (t :: _)) = Just t
tagOf _ = Nothing

||| A word, the value of one register of an integer type.
export
wordOf : Value enc v -> Maybe (Opnd v W64)
wordOf (MkValue [Word] [w]) = Just w
wordOf _ = Nothing

||| A double, the value of one register of `Double`.
export
doubleOf : Value enc v -> Maybe (Opnd v F64)
doubleOf (MkValue [Dbl] [f]) = Just f
doubleOf _ = Nothing

||| Zeros for the registers of the layout: what the registers of a sum's
||| other constructors hold.
export
zeros : (a : Layout) -> Build d c m v l (All (Opnd v) (tys a))
zeros [] = pure []
zeros (Word :: rs) = (W 0 ::) <$> zeros rs
zeros (Dbl :: rs) = do z <- emit1 (FConst 0.0); (z ::) <$> zeros rs
zeros (Uniform :: rs) = (Erased ::) <$> zeros rs

------------------------------------------------------------------------------
-- Shapes

||| Where a constructor's fields lie in a value of its data type: the tag,
||| if the type has several constructors, the registers before the fields,
||| theirs, and those after.
public export
record Placement where
  constructor MkPlacement
  tag : Maybe Int
  before : Layout
  own : Layout
  after : Layout

||| The constructor of the name among a data type's, and where its fields
||| lie. This and `Flat.Exp.sumSlices` are what every place that builds
||| or opens a sum reads.
export
placement : List ConShape -> Name -> Maybe (ConShape, Placement)
placement [] _ = Nothing
placement [c] n = if c.name == n then Just (c, MkPlacement Nothing [] (fieldsLayout c.fields) []) else Nothing
placement cs n = do
  i <- position cs 0
  c <- getAt i cs
  (b, o, a) <- sumSlices cs i
  pure (c, MkPlacement (Just c.tag) b o a)
  where
    position : List ConShape -> Nat -> Maybe Nat
    position [] _ = Nothing
    position (c :: cs') i = if c.name == n then Just i else position cs' (S i)

||| A constructor's value from its fields' registers: its tag, if its type
||| has several constructors, and zeros for the others' registers.
export
conValue : Placement -> Value enc v -> Build d c m v l (Value enc v)
conValue p fs = do
  b <- zeros p.before
  a <- zeros p.after
  let body = appendValues (MkValue p.before b) (appendValues fs (MkValue p.after a))
  pure $ case p.tag of
    Nothing => body
    Just t => appendValues (MkValue [Word] [W (cast t)]) body

||| The registers of a constructor's fields in a value of its data type.
export
fieldsOf : Placement -> Value enc v -> Maybe (Value enc v)
fieldsOf p val = do
  rest <- case p.tag of
    Nothing => Just val
    Just _ => snd <$> takeRegs [Word] val
  (_, rest') <- takeRegs p.before rest
  (own, _) <- takeRegs p.own rest'
  pure (MkValue p.own own)

------------------------------------------------------------------------------
-- Calls

||| A form that the program declares as a `Direct` function, as a call of it
||| needs it.
public export
record Callee (d : Decls enc) where
  constructor MkCallee
  form : FlatDef
  var : (n ** Var d.sigs (MkSig n (InDirect (tys form.result) False) (tys (paramsLayout form.params)) (convertsIn form.name)))

||| The forms the declarations have `Direct` functions for, by the forms'
||| names.
export
callees : (d : Decls enc) -> List FlatDef -> SortedMap Name (Callee d)
callees d fds = fromList (mapMaybe one (enumerate d.sigs))
  where
    byName : SortedMap Name FlatDef
    byName = fromList [(flatName fd.name, fd) | fd <- fds]

    one : (s ** Var d.sigs s) -> Maybe (Name, Callee d)
    one (MkSig n (InDirect rs False) ps cv ** var) = do
      fd <- lookup n byName
      case (decEq rs (tys fd.result), decEq ps (tys (paramsLayout fd.params)), decEq cv (convertsIn fd.name)) of
        (Yes Refl, Yes Refl, Yes Refl) => Just (fd.name, MkCallee fd (n ** var))
        _ => Nothing
    one _ = Nothing

||| Whether the expression calls the form.
calls : Name -> FlatExp -> Bool
calls n (FVar _ _) = False
calls n (FLet _ _ val sc) = calls n val || calls n sc
calls n (FConst _ _) = False
calls n (FOp _ _ as) = any (calls n) (toList as)
calls n (FCall _ f as) = f == n || any (calls n) as
calls n (FPrim _ _ _ _ as) = any (calls n) as
calls n (FCon _ _ _ _ _ as) = any (calls n) as
calls n (FCase _ sc alts def) = calls n sc || any alt alts || maybe False (calls n) def
  where
    alt : FlatAlt -> Bool
    alt (FConAlt _ _ _ b) = calls n b
    alt (FConstAlt _ b) = calls n b
calls n (FCrash _ _) = False
calls n (FNone _) = False

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
data Held = Narrower SubWord Bool | Whole Bool

||| How an integer type or `Char` is held; `Char` as its code point.
held : PrimType -> Maybe Held
held IntType = Just (Whole True)
held Int64Type = Just (Whole True)
held Bits64Type = Just (Whole False)
held Int8Type = Just (Narrower Sub8 True)
held Int16Type = Just (Narrower Sub16 True)
held Int32Type = Just (Narrower Sub32 True)
held Bits8Type = Just (Narrower Sub8 False)
held Bits16Type = Just (Narrower Sub16 False)
held Bits32Type = Just (Narrower Sub32 False)
held CharType = Just (Narrower Sub32 False)
held _ = Nothing

signed : Held -> Bool
signed (Narrower _ s) = s
signed (Whole s) = s

||| The unsigned relation for a signed one.
unsignedRel : Rel -> Rel
unsignedRel LtS = LtU
unsignedRel LeS = LeU
unsignedRel GtS = GtU
unsignedRel GeS = GeU
unsignedRel r = r

------------------------------------------------------------------------------
-- Intrinsics

||| The words of a value whose registers are all words.
words : Value enc v -> Maybe (List (Opnd v W64))
words (MkValue [] []) = Just []
words (MkValue (Word :: rs) (x :: xs)) = (x ::) <$> words (MkValue rs xs)
words _ = Nothing

------------------------------------------------------------------------------
-- The lowering

||| What the lowering of a form knows of the program: the forms it may call,
||| the shapes of the data types, and the OS services' externs, each bound to
||| the form of the function that implements it on the platform.
public export
record Forms (enc : Enc) (d : Decls enc) where
  constructor MkForms
  callees : SortedMap Name (Callee d)
  shapes : Shapes
  services : SortedMap Name Name

||| Each variable in scope: its type's skeleton and its value.
Env : (enc : Enc) -> (Ty enc -> Type) -> Type
Env enc v = SortedMap Name (Skeleton, Value enc v)

parameters {enc : Enc} (0 d : Decls enc) (pr : Forms enc d) (self : FlatDef) (m : Bool)
           {0 v : Ty enc -> Type} {0 l : List (Ty enc) -> Type}

  0 B : Type -> Type
  B = Build d (InDirect (tys self.result) False) m v l

  0 E : Type
  E = End d (InDirect (tys self.result) False) m v l

  0 Again : Type
  Again = Jumper d (InDirect (tys self.result) False) m v l (tys (paramsLayout self.params))

  ------------------------------------------------------------------------------
  -- Words and doubles

  word : Value enc v -> B (Opnd v W64)
  word x = maybe (unsupported "a word of another layout") pure (wordOf x)

  double : Value enc v -> B (Opnd v F64)
  double x = maybe (unsupported "a double of another layout") pure (doubleOf x)

  ||| A word wrapped to the type's width, extended again.
  wrap : Held -> Opnd v W64 -> B (Opnd v W64)
  wrap (Narrower sw s) w = emit1 (Ext sw s w)
  wrap (Whole _) w = pure w

  ||| A value of the primitive type.
  prim : PrimType -> Value enc v -> (Skeleton, Value enc v)
  prim t x = (SPrim t, x)

  wordVal : PrimType -> Opnd v W64 -> (Skeleton, Value enc v)
  wordVal t w = prim t (MkValue [Word] [w])

  doubleVal : Opnd v F64 -> (Skeleton, Value enc v)
  doubleVal f = prim DoubleType (MkValue [Dbl] [f])

  withHeld : PrimType -> String -> (Held -> B a) -> B a
  withHeld t what k = case held t of
    Just h => k h
    Nothing => unsupported (what ++ " on " ++ show t ++ " in a flat form")

  ||| A word as a `Char`: itself if it is a Unicode scalar value, 0 if not.
  toChar : Opnd v W64 -> B (Opnd v W64)
  toChar w = do
    [r] <- joinPoint [W64] $ \done => do
      keep <- block [] $ \[] => done [w]
      zero <- block [] $ \[] => done [W 0]
      branch LtS w (W 0) (zero []) $
        branch LeS w (W 55295) (keep []) $
          branch LtS w (W 57344) (zero []) $
            branch LeS w (W 1114111) (keep []) (zero [])
    pure r

  ||| A word of the integer type as a double. A `Bits64` at or above 2^63
  ||| is halved, its low bit kept for the rounding, converted and doubled.
  wordToDouble : Held -> Opnd v W64 -> B (Opnd v F64)
  wordToDouble (Whole False) w = do
    [f] <- joinPoint [F64] $ \done =>
      branch GeS w (W 0) (do f <- emit1 (Convert I2F w); done [f]) $ do
        h <- emit1 (Arith Shr w (W 1))
        b <- emit1 (Arith And w (W 1))
        hb <- emit1 (Arith Or h b)
        f <- emit1 (Convert I2F hb)
        f2 <- emit1 (FArith FAdd f f)
        done [f2]
    pure f
  wordToDouble _ w = emit1 (Convert I2F w)

  ||| A double truncated to the integer type. A `Bits64` at or above 2^63 is
  ||| converted less 2^63, which is added back to the word.
  doubleToWord : Held -> Opnd v F64 -> B (Opnd v W64)
  doubleToWord (Whole False) f = do
    big <- emit1 (FConst 9223372036854775808.0)
    above <- emit1 (FCmp GeS f big)
    [w] <- joinPoint [W64] $ \done =>
      branch EqR above (W 0) (do w <- emit1 (Convert F2I f); done [w]) $ do
        g <- emit1 (FArith FSub f big)
        w <- emit1 (Convert F2I g)
        w' <- emit1 (Arith Add w (W (-9223372036854775808)))
        done [w']
    pure w
  doubleToWord h f = do
    w <- emit1 (Convert F2I f)
    wrap h w

  ||| A cast between the primitive types.
  castTo : PrimType -> PrimType -> Value enc v -> B (Skeleton, Value enc v)
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

  arith : PrimType -> ArithOp -> FOp -> (x, y : Value enc v) -> B (Skeleton, Value enc v)
  arith DoubleType _ o x y = do a <- double x; b <- double y; doubleVal <$> emit1 (FArith o a b)
  arith t o _ x y = withHeld t "arithmetic" $ \h => do
    a <- word x
    b <- word y
    w <- emit1 (Arith o a b)
    wordVal t <$> wrap h w

  bitwise : PrimType -> ArithOp -> (x, y : Value enc v) -> B (Skeleton, Value enc v)
  bitwise t o x y = withHeld t "a bitwise operation" $ \h => do
    a <- word x
    b <- word y
    w <- emit1 (Arith o a b)
    wordVal t <$> wrap h w

  shifting : PrimType -> (left : Bool) -> (x, y : Value enc v) -> B (Skeleton, Value enc v)
  shifting t left x y = withHeld t "a shift" $ \h => do
    a <- word x
    k <- word y
    w <- shiftBy (if left then Shl else if signed h then Sar else Shr) a k
    wordVal t <$> wrap h w

  comparison : PrimType -> Rel -> (x, y : Value enc v) -> B (Skeleton, Value enc v)
  comparison DoubleType rel x y = do
    a <- double x
    b <- double y
    wordVal IntType <$> emit1 (FCmp rel a b)
  comparison t rel x y = withHeld t "a comparison" $ \h => do
    a <- word x
    b <- word y
    wordVal IntType <$> emit1 (Cmp (if signed h then rel else unsignedRel rel) a b)

  constant : Constant -> B (Skeleton, Value enc v)
  constant (Db x) = doubleVal <$> emit1 (FConst x)
  constant WorldVal = pure (SPrim WorldType, noRegs)
  constant k = case (constType k, constWord k) of
    (Just t, Just w) => pure (wordVal t (W w))
    _ => unsupported ("the constant " ++ show k ++ " in a flat form")

  ||| A primitive operation.
  primOp : PrimFn n -> Vect n (Value enc v) -> B (Skeleton, Value enc v)
  primOp (Add t) [x, y] = arith t Add FAdd x y
  primOp (Sub t) [x, y] = arith t Sub FSub x y
  primOp (Mul t) [x, y] = arith t Mul FMul x y
  primOp (Div DoubleType) [x, y] = do a <- double x; b <- double y; doubleVal <$> emit1 (FArith FDiv a b)
  primOp (Div t) [x, y] = withHeld t "division" $ \h => do
    a <- word x
    b <- word y
    nonZero b
    w <- divide (signed h) False a b
    wordVal t <$> wrap h w
  primOp (Mod t) [x, y] = withHeld t "remainder" $ \h => do
    a <- word x
    b <- word y
    nonZero b
    w <- divide (signed h) True a b
    wordVal t <$> wrap h w
  primOp (Neg DoubleType) [x] = do a <- double x; doubleVal <$> emit1 (FNeg a)
  primOp (Neg t) [x] = withHeld t "negation" $ \h => do
    a <- word x
    w <- emit1 (Unary Negate a)
    wordVal t <$> wrap h w
  primOp (ShiftL t) [x, y] = shifting t True x y
  primOp (ShiftR t) [x, y] = shifting t False x y
  primOp (BAnd t) [x, y] = bitwise t And x y
  primOp (BOr t) [x, y] = bitwise t Or x y
  primOp (BXOr t) [x, y] = bitwise t Xor x y
  primOp (LT t) [x, y] = comparison t LtS x y
  primOp (LTE t) [x, y] = comparison t LeS x y
  primOp (EQ t) [x, y] = comparison t EqR x y
  primOp (GTE t) [x, y] = comparison t GeS x y
  primOp (GT t) [x, y] = comparison t GtS x y
  primOp (Cast from to) [x] = castTo from to x
  primOp op _ = unsupported ("the primitive " ++ show op ++ " in a flat form")

  ------------------------------------------------------------------------------
  -- Expressions

  ||| The skeleton and layout of an expression's value, from the variables'
  ||| and the callees' results.
  typeOf : SortedMap Name (Skeleton, Layout) -> FlatExp -> Maybe (Skeleton, Layout)
  typeOf env = expType (\x => lookup x env)
                       (\n => (\c => (c.form.resultSkeleton, c.form.result)) <$> lookup n pr.callees)

  layouts : Env enc v -> SortedMap Name (Skeleton, Layout)
  layouts = map (\(sk, x) => (sk, x.layout))

  ||| The variables of an alternative, bound to the registers of the fields.
  bindFields : Env enc v -> List FlatVar -> Value enc v -> Maybe (Env enc v)
  bindFields env [] (MkValue [] []) = Just env
  bindFields env [] _ = Nothing
  bindFields env (fv :: fvs) val = do
    (xs, rest) <- takeRegs fv.layout val
    bindFields (insert fv.name (fv.skeleton, MkValue fv.layout xs) env) fvs rest

  mutual
    ||| An expression's value, and its type's skeleton.
    expr : Env enc v -> FlatExp -> B (Skeleton, Value enc v)
    expr env (FVar _ x) = case lookup x env of
      Just t => pure t
      Nothing => unsupported ("the unbound variable " ++ show x ++ " in a flat form")
    expr env (FLet _ fv val sc) = do
      env' <- bind env fv val
      expr env' sc
    expr env (FConst _ k) = constant k
    expr env (FOp _ op args) = do
      xs <- traverse (\a => snd <$> expr env a) args
      primOp op xs
    expr env (FCall _ n args) = do
      xs <- traverse (\a => snd <$> expr env a) args
      callForm n xs
    expr env (FPrim _ n sk lay args) = case intrinsicOf {enc} n of
      Nothing => case lookup n pr.services of
        -- an OS service: a call of the platform's function for it
        Just f => do
          xs <- traverse (\a => snd <$> expr env a) args
          (_, x) <- callForm f xs
          maybe (unsupported ("the OS service " ++ show n ++ ", whose result is not its type's"))
                (\rs => pure (sk, MkValue lay rs)) (regsAs lay x)
        Nothing => unsupported ("the primitive " ++ show n ++ " in a flat form")
      Just i => do
        xs <- traverse (\a => snd <$> expr env a) args
        x <- intrinsic n i (concatValues xs)
        maybe (unsupported ("the intrinsic " ++ show n ++ ", whose result is not its type's"))
              (\rs => pure (sk, MkValue lay rs)) (regsAs lay x)
    expr env (FCon _ c _ sk lay args) = do
      xs <- traverse (\a => snd <$> expr env a) args
      x <- construct sk c (concatValues xs)
      case regsAs lay x of
        Just rs => pure (sk, MkValue lay rs)
        Nothing => unsupported ("the constructor " ++ show c ++ ", whose layout is not its type's")
    expr env e@(FCase _ scr alts def) = case typeOf (layouts env) e of
      Nothing => do
        _ <- joinPoint [] $ \exit => dispatch env scr alts def (\env', b => do _ <- expr env' b; exit [])
        unsupported "a case that has no value"
      Just (sk, lay) => do
        rs <- joinPoint (tys lay) $ \exit =>
          dispatch env scr alts def $ \env', b => do
            (_, x) <- expr env' b
            maybe (unsupported "an alternative of another layout") exit (regsAs lay x)
        pure (sk, MkValue lay rs)
    expr env (FCrash _ msg) = crash msg
    expr env (FNone _) = pure (SOther, noRegs)

    ||| An intrinsic's instructions, from its arguments' registers.
    intrinsic : Name -> Intrinsic -> Value enc v -> B (Value enc v)
    -- a uniform value and a pointer word: the conversions, so this module's
    -- functions alone
    intrinsic n (ObjectWord k) (MkValue [Uniform] [u]) = case m of
      True => do
        p <- emit1 (NarrowPtr k u)
        w <- emit1 (AddrToWord p)
        pure (MkValue [Word] [w])
      False => unsupported ("the intrinsic " ++ show n ++ " outside the memory module")
    intrinsic n (WordObject k) (MkValue [Word] [w]) = case m of
      True => do
        p <- emit1 (WordToAddr k w)
        u <- emit1 (WidenPtr p)
        pure (MkValue [Uniform] [u])
      False => unsupported ("the intrinsic " ++ show n ++ " outside the memory module")
    intrinsic n i x = case words x of
      Just ws => wordIntrinsic n i ws
      Nothing => unsupported ("the intrinsic " ++ show n ++ " on registers of another kind")

    ||| An intrinsic on words.
    wordIntrinsic : Name -> Intrinsic -> List (Opnd v W64) -> B (Value enc v)
    wordIntrinsic _ Syscall6 [n, a, b, c, e, f, g] = do
      r <- emit1 (SystemCall n [a, b, c, e, f, g])
      pure (MkValue [Word] [r])
    wordIntrinsic _ Load64 [base, off] = do
      p <- emit1 (Arith Add base off)
      r <- emit1 (Load W64 (MkMem (AtWord p) Nothing 0))
      pure (MkValue [Word] [r])
    wordIntrinsic _ (LoadNarrow sw) [base, off] = do
      p <- emit1 (Arith Add base off)
      r <- emit1 (LoadN sw False (MkMem (AtWord p) Nothing 0))
      pure (MkValue [Word] [r])
    wordIntrinsic _ Store64 [base, off, x] = do
      p <- emit1 (Arith Add base off)
      emit0 (Store W64 (MkMem (AtWord p) Nothing 0) x)
      pure noRegs
    wordIntrinsic _ (StoreNarrow sw) [base, off, x] = do
      p <- emit1 (Arith Add base off)
      emit0 (StoreN sw (MkMem (AtWord p) Nothing 0) x)
      pure noRegs
    wordIntrinsic _ GetHp [] = do
      w <- emit1 ReadHp
      pure (MkValue [Word] [w])
    wordIntrinsic _ SetHp [w] = do
      emit0 (WriteHp w)
      pure noRegs
    wordIntrinsic _ GetHpLim [] = do
      w <- emit1 ReadHpLim
      pure (MkValue [Word] [w])
    wordIntrinsic _ SetHpLim [w] = do
      emit0 (WriteHpLim w)
      pure noRegs
    -- the continuation is a pointer: its word needs the conversions
    wordIntrinsic n GetK [] = case m of
      True => do
        k <- emit1 ReadK
        w <- emit1 (AddrToWord k)
        pure (MkValue [Word] [w])
      False => unsupported ("the intrinsic " ++ show n ++ " outside the memory module")
    wordIntrinsic n SetK [w] = case m of
      True => do
        k <- emit1 (WordToAddr CONT w)
        emit0 (WriteK k)
        pure noRegs
      False => unsupported ("the intrinsic " ++ show n ++ " outside the memory module")
    wordIntrinsic _ PointerTag [] = pure (MkValue [Word] [W (cast (pointerTag enc.val))])
    wordIntrinsic _ (AreaAddress a) [] = do
      p <- emit1 (AreaAddr a)
      pure (MkValue [Word] [p])
    wordIntrinsic n _ _ = unsupported ("the intrinsic " ++ show n ++ " with another number of arguments")

    ||| A `let`: the variable bound to the value.
    bind : Env enc v -> FlatVar -> FlatExp -> B (Env enc v)
    bind env fv val = do
      (_, x) <- expr env val
      case regsAs fv.layout x of
        Just rs => pure (insert fv.name (fv.skeleton, MkValue fv.layout rs) env)
        Nothing => unsupported ("the value of " ++ show fv.name ++ ", whose layout is not its type's")

    ||| A call of a form.
    callForm : Name -> List (Value enc v) -> B (Skeleton, Value enc v)
    callForm n xs = case lookup n pr.callees of
      Nothing => unsupported ("a call of " ++ show n ++ ", which has no flat form in the program")
      Just (MkCallee fd (_ ** var)) => case regsAs (paramsLayout fd.params) (concatValues xs) of
        Nothing => unsupported ("a call of " ++ show n ++ " with arguments of other layouts")
        Just args => do
          rs <- directCall var args
          pure (fd.resultSkeleton, MkValue fd.result rs)

    ||| A constructor's value, from its fields'.
    construct : Skeleton -> Name -> Value enc v -> B (Value enc v)
    construct sk c fs = case shapeOf pr.shapes sk of
      Just (DataShape cs) => case placement cs c of
        Just (_, p) => conValue p fs
        Nothing => unsupported ("the constructor " ++ show c ++ ", which is not one of " ++ show sk)
      _ => unsupported ("a constructor of " ++ show sk ++ ", whose shape is not known")

    ||| A case: the scrutinee, then each alternative's body as `k` lowers it,
    ||| in the environment of its variables.
    dispatch : Env enc v -> FlatExp -> List FlatAlt -> Maybe FlatExp -> (Env enc v -> FlatExp -> E) -> E
    dispatch env scr alts def k = do
      (sk, x) <- expr env scr
      let other = maybe (crash "no case alternative matched") (k env) def
      case alts of
        [] => other
        FConstAlt _ _ :: _ => constCase env x alts other k
        FConAlt _ _ _ _ :: _ => conCase env sk x alts other k

    constCase : Env enc v -> Value enc v -> List FlatAlt -> E -> (Env enc v -> FlatExp -> E) -> E
    constCase env x alts other k = do
      w <- word x
      let cs = mapMaybe (\a => case a of
                                 FConstAlt c b => (\i => (i, k env b)) <$> constWord c
                                 _ => Nothing) alts
      if length cs /= length alts then unsupported "a case on constants that are not words" else
        case choose (distinct (map fst cs) && keysFit (W64 {enc}) (map fst cs)) of
          Left ok => switch w cs other
          Right _ => unsupported "a case with repeated constants"

    conCase : Env enc v -> Skeleton -> Value enc v -> List FlatAlt -> E -> (Env enc v -> FlatExp -> E) -> E
    conCase env sk x alts other k = case shapeOf pr.shapes sk of
      Just (DataShape [c]) => case find (named c.name) alts of
        Just (FConAlt _ _ vs b) => alternative env (MkPlacement Nothing [] (fieldsLayout c.fields) []) x vs b k
        _ => other
      Just (DataShape cs) => do
        t <- maybe (unsupported "a sum without its tag") pure (tagOf x)
        let branches = mapMaybe (\a => case a of
                                         FConAlt cn _ vs b => do
                                           (c, p) <- placement cs cn
                                           pure (the Int64 (cast c.tag), alternative env p x vs b k)
                                         _ => Nothing) alts
        if length branches /= length alts then unsupported ("a case on a constructor that is not one of " ++ show sk) else
          case choose (distinct (map fst branches) && keysFit (W64 {enc}) (map fst branches)) of
            Left ok => switch t branches other
            Right _ => unsupported "a case with repeated constructors"
      _ => unsupported ("a case on " ++ show sk ++ ", whose shape is not known")
      where
        named : Name -> FlatAlt -> Bool
        named n (FConAlt cn _ _ _) = cn == n
        named _ _ = False

    alternative : Env enc v -> Placement -> Value enc v -> List FlatVar -> FlatExp ->
                  (Env enc v -> FlatExp -> E) -> E
    alternative env p x vs b k = case fieldsOf p x >>= bindFields env vs of
      Just env' => k env' b
      Nothing => unsupported "an alternative whose fields are not its constructor's"

  ||| The expression's value, returned.
  returned : Env enc v -> FlatExp -> E
  returned env e = do
    (_, x) <- expr env e
    maybe (unsupported "a result whose layout is not the form's") ret (regsAs self.result x)

  ||| An expression in tail position: its value is the result, and a call of
  ||| the form itself jumps back to its start.
  tailExp : Env enc v -> Maybe Again -> FlatExp -> E
  tailExp env again (FLet _ fv val sc) = do
    env' <- bind env fv val
    tailExp env' again sc
  tailExp env again (FCase _ scr alts def) = dispatch env scr alts def (\env', b => tailExp env' again b)
  tailExp env (Just again) e@(FCall _ n args) =
    if n /= self.name then returned env e else do
      xs <- traverse (\a => snd <$> expr env a) args
      maybe (unsupported "a call of the form itself with arguments of other layouts") again
            (regsAs (paramsLayout self.params) (concatValues xs))
  tailExp env _ (FCrash _ msg) = crash msg
  tailExp env _ e = returned env e

  ||| The form's body, from the parameters' registers.
  formBody : Maybe Again -> All (Opnd v) (tys (paramsLayout self.params)) -> E
  formBody again xs = case bindFields empty self.params (MkValue (paramsLayout self.params) xs) of
    Just env => tailExp env again self.body
    Nothing => unsupported "parameters whose layouts are not their types'"

||| A form as the body of its `Direct` function. A form that calls itself
||| is a loop, which a call in tail position jumps back to.
export
lowerForm : {enc : Enc} -> (0 d : Decls enc) -> Forms enc d -> (fd : FlatDef) ->
            Closed d (InDirect (tys fd.result) False) (convertsIn fd.name) (tys (paramsLayout fd.params))
lowerForm d pr fd = build $ \xs =>
  if calls fd.name fd.body
     then loop (tys (paramsLayout fd.params)) xs $ \again, ys => formBody d pr fd (convertsIn fd.name) (Just again) ys
     else formBody d pr fd (convertsIn fd.name) Nothing xs
