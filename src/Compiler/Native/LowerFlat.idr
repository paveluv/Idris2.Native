||| The flat lowering: a flat form (`Flat.Exp`) to a `Direct` function of
||| the term IR (`Compiler.Native.TermIR`), written through the builder.
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
||| collects. A `case` on a sum is a switch on the tag, and one that is not
||| in tail position a join, whose parameters are the case's registers. A
||| call of a form is a `DirectCall`; a call of the form itself in tail
||| position jumps back to its start, so self tail recursion is a loop. The
||| `%extern` and `%foreign` primitives (`FPrim`), the operations on strings
||| and the double functions of the C library lower to `Unsupported`.
module Compiler.Native.LowerFlat

import Compiler.Native.Words
import Flat.Exp
import Core.Name
import Core.TT
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.Vect
import Decidable.Equality

%default covering

------------------------------------------------------------------------------
-- Registers

export
DecEq Rep where
  decEq Word Word = Yes Refl
  decEq Dbl Dbl = Yes Refl
  decEq Word Dbl = No (\case Refl impossible)
  decEq Dbl Word = No (\case Refl impossible)

||| The type of a register of the representation.
public export
repTy : Rep -> Ty enc
repTy Word = W64
repTy Dbl = F64

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

||| The name of a form's `Direct` function. A form has its function's name,
||| which the function's ordinary code keeps.
export
flatName : Name -> Name
flatName n = NS (mkNamespace "_flat") n

||| The signature of a form's `Direct` function.
export
formSig : FlatDef -> Sig enc
formSig fd = MkSig (flatName fd.name) (InDirect (tys fd.result) False) (tys (paramsLayout fd.params)) False

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

------------------------------------------------------------------------------
-- Shapes

||| The shapes of the data types the forms handle, by skeleton.
public export
Shapes : Type
Shapes = List (Skeleton, Shape)

||| A type's shape: a primitive's is its own.
export
shapeOf : Shapes -> Skeleton -> Maybe Shape
shapeOf ss (SPrim t) = Just (PrimShape t)
shapeOf ss sk = lookup sk ss

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
  var : (n ** Var d.sigs (MkSig n (InDirect (tys form.result) False) (tys (paramsLayout form.params)) False))

||| The forms the declarations have `Direct` functions for, by the forms'
||| names.
export
callees : (d : Decls enc) -> List FlatDef -> SortedMap Name (Callee d)
callees d fds = fromList (mapMaybe one (enumerate d.sigs))
  where
    byName : SortedMap Name FlatDef
    byName = fromList [(flatName fd.name, fd) | fd <- fds]

    one : (s ** Var d.sigs s) -> Maybe (Name, Callee d)
    one (MkSig n (InDirect rs False) ps False ** var) = do
      fd <- lookup n byName
      case (decEq rs (tys fd.result), decEq ps (tys (paramsLayout fd.params))) of
        (Yes Refl, Yes Refl) => Just (fd.name, MkCallee fd (n ** var))
        _ => Nothing
    one _ = Nothing

||| Whether the expression calls the form.
calls : Name -> FlatExp -> Bool
calls n (FVar _ _) = False
calls n (FLet _ _ val sc) = calls n val || calls n sc
calls n (FConst _ _) = False
calls n (FOp _ _ as) = any (calls n) (toList as)
calls n (FCall _ f as) = f == n || any (calls n) as
calls n (FPrim _ _ as) = any (calls n) as
calls n (FCon _ _ _ _ _ as) = any (calls n) as
calls n (FCase _ sc alts def) = calls n sc || any alt alts || maybe False (calls n) def
  where
    alt : FlatAlt -> Bool
    alt (FConAlt _ _ _ b) = calls n b
    alt (FConstAlt _ b) = calls n b
calls n (FCrash _ _) = False
calls n (FNone _) = False

||| The forms a form calls.
export
formCallees : FlatDef -> List Name
formCallees fd = go fd.body
  where
    go : FlatExp -> List Name
    go (FVar _ _) = []
    go (FLet _ _ val sc) = go val ++ go sc
    go (FConst _ _) = []
    go (FOp _ _ as) = concatMap go (toList as)
    go (FCall _ f as) = f :: concatMap go as
    go (FPrim _ _ as) = concatMap go as
    go (FCon _ _ _ _ _ as) = concatMap go as
    go (FCase _ sc alts def) = go sc ++ concatMap alt alts ++ maybe [] go def
      where
        alt : FlatAlt -> List Name
        alt (FConAlt _ _ _ b) = go b
        alt (FConstAlt _ b) = go b
    go (FCrash _ _) = []
    go (FNone _) = []

||| The skeletons of the types a form handles: its parameters', its
||| result's, its variables' and its constructors'. The lowering needs the
||| shapes of the data types among them.
export
formSkeletons : FlatDef -> List Skeleton
formSkeletons fd = fd.resultSkeleton :: map skeleton fd.params ++ go fd.body
  where
    go : FlatExp -> List Skeleton
    go (FVar _ _) = []
    go (FLet _ fv val sc) = fv.skeleton :: go val ++ go sc
    go (FConst _ _) = []
    go (FOp _ _ as) = concatMap go (toList as)
    go (FCall _ _ as) = concatMap go as
    go (FPrim _ _ as) = concatMap go as
    go (FCon _ _ _ sk _ as) = sk :: concatMap go as
    go (FCase _ sc alts def) = go sc ++ concatMap alt alts ++ maybe [] go def
      where
        alt : FlatAlt -> List Skeleton
        alt (FConAlt _ _ vs b) = map skeleton vs ++ go b
        alt (FConstAlt _ b) = go b
    go (FCrash _ _) = []
    go (FNone _) = []

------------------------------------------------------------------------------
-- Primitive types and operations

||| The layout of a primitive type.
primLayout : PrimType -> Layout
primLayout DoubleType = [Dbl]
primLayout WorldType = []
primLayout _ = [Word]

||| The type of a constant.
constType : Constant -> Maybe PrimType
constType (I _) = Just IntType
constType (I8 _) = Just Int8Type
constType (I16 _) = Just Int16Type
constType (I32 _) = Just Int32Type
constType (I64 _) = Just Int64Type
constType (BI _) = Just IntegerType
constType (B8 _) = Just Bits8Type
constType (B16 _) = Just Bits16Type
constType (B32 _) = Just Bits32Type
constType (B64 _) = Just Bits64Type
constType (Str _) = Just StringType
constType (Ch _) = Just CharType
constType (Db _) = Just DoubleType
constType WorldVal = Just WorldType
constType (PrT _) = Nothing

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

||| The type of a primitive operation's result.
opResult : PrimFn n -> Maybe PrimType
opResult (Add t) = Just t
opResult (Sub t) = Just t
opResult (Mul t) = Just t
opResult (Div t) = Just t
opResult (Mod t) = Just t
opResult (Neg t) = Just t
opResult (ShiftL t) = Just t
opResult (ShiftR t) = Just t
opResult (BAnd t) = Just t
opResult (BOr t) = Just t
opResult (BXOr t) = Just t
opResult (LT _) = Just IntType
opResult (LTE _) = Just IntType
opResult (EQ _) = Just IntType
opResult (GTE _) = Just IntType
opResult (GT _) = Just IntType
opResult (Cast _ t) = Just t
opResult _ = Nothing

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
-- The lowering

||| What the lowering of a form knows of the program: the forms it may call,
||| and the shapes of the data types.
public export
record Forms (enc : Enc) (d : Decls enc) where
  constructor MkForms
  callees : SortedMap Name (Callee d)
  shapes : Shapes

||| Each variable in scope: its type's skeleton and its value.
Env : (enc : Enc) -> (Ty enc -> Type) -> Type
Env enc v = SortedMap Name (Skeleton, Value enc v)

parameters {enc : Enc} (d : Decls enc) (pr : Forms enc d) (self : FlatDef)
           {0 v : Ty enc -> Type} {0 l : List (Ty enc) -> Type}

  0 B : Type -> Type
  B = Build d (InDirect (tys self.result) False) False v l

  0 E : Type
  E = End d (InDirect (tys self.result) False) False v l

  0 Again : Type
  Again = Jumper d (InDirect (tys self.result) False) False v l (tys (paramsLayout self.params))

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

  ||| The skeleton and layout of an expression's value, from the variables'.
  ||| Nothing if no value comes of it: a crash, or every alternative of a
  ||| case one.
  typeOf : SortedMap Name (Skeleton, Layout) -> FlatExp -> Maybe (Skeleton, Layout)
  typeOf env (FVar _ x) = lookup x env
  typeOf env (FLet _ fv _ sc) = typeOf (insert fv.name (fv.skeleton, fv.layout) env) sc
  typeOf env (FConst _ k) = (\t => (SPrim t, primLayout t)) <$> constType k
  typeOf env (FOp _ op _) = (\t => (SPrim t, primLayout t)) <$> opResult op
  typeOf env (FCall _ n _) = (\c => (c.form.resultSkeleton, c.form.result)) <$> lookup n pr.callees
  typeOf env (FPrim _ _ _) = Nothing
  typeOf env (FCon _ _ _ sk lay _) = Just (sk, lay)
  typeOf env (FCase _ _ alts def) = head' (catMaybes (map alt alts ++ [def >>= typeOf env]))
    where
      alt : FlatAlt -> Maybe (Skeleton, Layout)
      alt (FConAlt _ _ vs b) = typeOf (foldl (\e, fv => insert fv.name (fv.skeleton, fv.layout) e) env vs) b
      alt (FConstAlt _ b) = typeOf env b
  typeOf env (FCrash _ _) = Nothing
  typeOf env (FNone _) = Just (SOther, [])

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
    expr env (FPrim _ n _) = unsupported ("the primitive " ++ show n ++ " in a flat form")
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
lowerForm : {enc : Enc} -> (d : Decls enc) -> Forms enc d -> (fd : FlatDef) ->
            Closed d (InDirect (tys fd.result) False) False (tys (paramsLayout fd.params))
lowerForm d pr fd = build $ \xs =>
  if calls fd.name fd.body
     then loop (tys (paramsLayout fd.params)) xs $ \again, ys => formBody d pr fd (Just again) ys
     else formBody d pr fd Nothing xs
