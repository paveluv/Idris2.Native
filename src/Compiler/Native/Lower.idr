||| The produce pass: VMCode and flat forms to the typed term
||| (`Compiler.Native.TermIR`), from which register allocation
||| (`Compiler.Native.RegAlloc`) makes the located IR.
|||
||| Every VMCode function becomes a `CPS` function of `Val` parameters,
||| written in `Build` (`Compiler.Native.TermIR.Build`), so Idris
||| checks its scoping and types when this module is compiled. VMCode's
||| locals are mutable; the term's values are not. The locals are therefore
||| an environment, from each local to the operand it holds, threaded through
||| the lowering: an `ASSIGN` is no code, and a constant is an immediate. A
||| `CASE` or `CONSTCASE` is a join point whose parameters are the locals its
||| alternatives assign and the code after it reads, so that code is lowered
||| once; in tail position the alternatives return directly. A non-tail call
||| or application has the rest of the code as its continuation. What is
||| live where is computed when the term becomes IR (`Compiler.Native.RegAlloc`).
|||
||| The program's declarations are fixed before any body is lowered: a
||| signature for each function and foreign function, one for each runtime
||| routine the lowering calls, and the static objects, which a pass over the
||| bodies collects first: the nullary constructors, and the integer
||| constants outside the fixnum range, those that casts of constants make
||| included.
|||
||| What v0 lowers: integer constants, those outside the fixnum range as
||| static objects; every integer type's arithmetic, bitwise operations,
||| shifts, division and comparisons, each wrapping to the type's width, and
||| the casts among the integer types and characters ("Integers", below);
||| constructors, nullary ones as shared statics; closures; application;
||| calls and tail calls; cases on constructors and on integer and character
||| constants; projection; the arrays behind `Data.IOArray` ("Arrays",
||| below); and the foreign `System.prim__exit`. Everything else lowers to
||| `Unsupported`, the abort stub, so a program always links and fails only
||| on the paths it reaches.
|||
||| A function that has a flat form (`Flat.Exp`) is not lowered from its
||| VMCode: the form becomes a `Direct` function (`Compiler.Native.LowerFlat`),
||| and the function a wrapper around it, the boundary between ordinary code
||| and flat code.
||| The wrapper takes each argument apart into the form's registers, calls
||| the form, and builds the result from the form's registers, each value as
||| ordinary code represents its type: an integer as above, a `Double` as a
||| `DOUBLE` box, and a data type by its constructors (`Flat.Exp.Ordinary`),
||| an enumeration's as fixnums of their tags, a newtype's as its field, and
||| any other as an object, a static one if it has no fields. A function whose
||| arity is not its form's, or one of whose types' shapes is not known, is
||| lowered from its VMCode as any other.
|||
||| Constructor ids are the per-type numbers VMCode gives constructors (its
||| `tag`): a `CASE` carries no type, so a global numbering cannot be
||| computed here, and every nullary constructor with the same id is the
||| same static object.
module Compiler.Native.Lower

import Compiler.Native.HeapObject
import Compiler.Native.IRCommon
import Compiler.Native.Linkage
import Compiler.Native.LowerFlat
import Compiler.Native.Platform
import Compiler.Native.Strings
import Compiler.Native.TermIR
import Compiler.Native.TermIR.Build
import Compiler.Native.Words
import Compiler.VMCode
import Core.CompileExpr
import Core.Name
import Core.TT
import Data.Builder
import Data.List
import Data.List.Quantifiers
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Data.Vect
import Decidable.Equality
import Decidable.Equality.Core
import Flat.Exp

%default covering


------------------------------------------------------------------------------
-- Names the lowering introduces

||| One of the `%extern` array primitives of `Data.IOArray.Prims`.
arrayPrim : String -> Name
arrayPrim s = NS (mkNamespace "Data.IOArray.Prims") (UN (Basic s))

||| The static object for every nullary constructor with this constructor id.
export
nullaryCon : Int -> Name
nullaryCon conId = NS (mkNamespace "_native") (UN (Basic ("con" ++ show conId)))

||| The function the program starts with.
export
mainExpression : Name
mainExpression = MN "__mainExpression" 0

------------------------------------------------------------------------------
-- Integers
--
-- Every integer type wraps to its width, as Idris's do, except `Integer`,
-- which is unbounded. In a uniform slot a narrow integer, of fewer than 64
-- bits, is always a fixnum. A 64-bit one is its bit pattern: a fixnum when the
-- pattern's signed value is in the fixnum range, and an `INT64` box holding
-- the pattern otherwise, so that the 64-bit types share one form and convert
-- among themselves for free. An `Integer` is a fixnum or a `BIGNUM`.
--
-- The locals are uniform, so an operation reads and writes uniform values. On
-- fixnums it works on the `Fix`es; otherwise, and when the result leaves the
-- fixnums, a narrow or 64-bit operation works on the words, a 64-bit result
-- being tagged if it fits and boxed if not, and an `Integer` operation calls
-- the runtime's routine on the original operands.

||| How an integer type is held, and how it wraps.
data IntWidth
  = ||| Fewer than 64 bits, signed or not: always a fixnum.
    Narrow Nat Bool
  | ||| 64 bits, signed or not: a fixnum or an `INT64` box, by its pattern.
    Wide Bool
  | ||| `Integer`: a fixnum or a `BIGNUM`.
    Unbounded

||| The width of an integer type. A `Char` counts as an unsigned narrow
||| integer, its code point, except as the target of a cast.
intWidth : PrimType -> Maybe IntWidth
intWidth IntType = Just (Wide True)
intWidth Int64Type = Just (Wide True)
intWidth Bits64Type = Just (Wide False)
intWidth Int8Type = Just (Narrow 8 True)
intWidth Int16Type = Just (Narrow 16 True)
intWidth Int32Type = Just (Narrow 32 True)
intWidth Bits8Type = Just (Narrow 8 False)
intWidth Bits16Type = Just (Narrow 16 False)
intWidth Bits32Type = Just (Narrow 32 False)
intWidth CharType = Just (Narrow 32 False)
intWidth IntegerType = Just Unbounded
intWidth _ = Nothing

||| An integer constant: its type's width and its value.
intConst : Constant -> Maybe (IntWidth, Integer)
intConst (I n) = Just (Wide True, cast n)
intConst (I8 n) = Just (Narrow 8 True, cast n)
intConst (I16 n) = Just (Narrow 16 True, cast n)
intConst (I32 n) = Just (Narrow 32 True, cast n)
intConst (I64 n) = Just (Wide True, cast n)
intConst (BI n) = Just (Unbounded, n)
intConst (B8 n) = Just (Narrow 8 False, cast n)
intConst (B16 n) = Just (Narrow 16 False, cast n)
intConst (B32 n) = Just (Narrow 32 False, cast n)
intConst (B64 n) = Just (Wide False, cast n)
intConst (Ch c) = Just (Narrow 32 False, cast (ord c))
intConst _ = Nothing

||| The signed value of a 64-bit pattern, from its value read signed or not.
patternValue : Integer -> Integer
patternValue v = if v >= 9223372036854775808 then v - 18446744073709551616 else v

subWord : Nat -> SubWord
subWord 8 = Sub8
subWord 16 = Sub16
subWord _ = Sub32

||| The unsigned relation for a signed one.
unsignedRel : Rel -> Rel
unsignedRel LtS = LtU
unsignedRel LeS = LeU
unsignedRel GtS = GtU
unsignedRel GeS = GeU
unsignedRel r = r

||| Whether the operation on two fixnums can leave the fixnum range.
overflows : ArithOp -> Bool
overflows Add = True
overflows Sub = True
overflows Mul = True
overflows _ = False

||| Whether every value of the first width is a value of the second, held the
||| same way, so that a cast between them is a move.
keeps : IntWidth -> IntWidth -> Bool
keeps (Wide _) (Wide _) = True
keeps (Narrow _ _) (Wide _) = True
keeps (Narrow _ _) Unbounded = True
keeps Unbounded Unbounded = True
keeps (Narrow n s) (Narrow m t) = if s == t then m >= n else not s && t && m > n
keeps _ _ = False

||| The static object of a 64-bit integer constant outside the fixnum range,
||| by the signed value of its pattern.
int64Static : Integer -> Name
int64Static p = NS (mkNamespace "_native") (UN (Basic ("int64_" ++ show p)))

||| The static object of an `Integer` constant outside the fixnum range.
bignumStatic : Integer -> Name
bignumStatic v = NS (mkNamespace "_native") (UN (Basic ("integer_" ++ show v)))

||| The static object of a string literal: one per distinct literal.
stringStatic : String -> Name
stringStatic s = NS (mkNamespace "_native") (UN (Basic ("string_" ++ show s)))

||| A cast of an integer constant to an integer type or to `Char`, done while
||| compiling, wrapping as the cast does at run time: Idris writes a literal
||| of a fixed-width type as an `Integer` constant and a cast.
castConstant : PrimType -> Integer -> Maybe Constant
castConstant IntType v = Just (I (cast v))
castConstant Int8Type v = Just (I8 (cast v))
castConstant Int16Type v = Just (I16 (cast v))
castConstant Int32Type v = Just (I32 (cast v))
castConstant Int64Type v = Just (I64 (cast v))
castConstant Bits8Type v = Just (B8 (cast v))
castConstant Bits16Type v = Just (B16 (cast v))
castConstant Bits32Type v = Just (B32 (cast v))
castConstant Bits64Type v = Just (B64 (cast v))
castConstant IntegerType v = Just (BI v)
castConstant CharType v =
  Just (Ch (if (v >= 0 && v <= 55295) || (v >= 57344 && v <= 1114111) then chr (cast v) else '\0'))
castConstant _ _ = Nothing


------------------------------------------------------------------------------
-- The program's declarations

-- The produce pass does not depend on the encoding of uniform values: it
-- writes integers, and the rendering encodes them. It only needs the value
-- encoding to have fixnums, since its integers are `Fix`es, and the bignum
-- encoding, to lay out the `BIGNUM`s of big constants.

||| The key of a VMCode register in the environment; `RVal` is the result.
key : Reg -> Maybe Int
key RVal = Just (-1)
key (Loc i) = Just i
key Discard = Nothing

||| What a static object of the program holds.
data StaticPlan
  = ||| Every nullary constructor with this id.
    Nullary Int
  | ||| A 64-bit pattern outside the fixnum range, by its signed value.
    Boxed Integer
  | ||| An `Integer` outside the fixnum range, and its magnitude's words.
    Big Integer
  | ||| A string literal.
    Text String

||| The constants a function's locals may hold, and the static objects its
||| constants need. A cast of a local holding a constant is folded while
||| compiling, so every constant a local may hold is followed through casts;
||| the result may name statics the lowering does not use, which costs only
||| their bytes.
staticsOf : List VMInst -> SortedMap Name StaticPlan
staticsOf body = snd (go body (empty, empty))
  where
    plan : Constant -> Maybe (Name, StaticPlan)
    plan k = case intConst k of
      Just (Wide _, v) => let p = patternValue v in
                          if inFixnumRange p then Nothing else Just (int64Static p, Boxed p)
      Just (Unbounded, v) => if inFixnumRange v then Nothing else Just (bignumStatic v, Big v)
      _ => case k of
        Str s => Just (stringStatic s, Text s)
        _ => Nothing

    note : Constant -> SortedMap Name StaticPlan -> SortedMap Name StaticPlan
    note k ss = case plan k of
      Just (n, p) => insert n p ss
      Nothing => ss

    add : Int -> Constant -> (SortedMap Int (List Constant), SortedMap Name StaticPlan) ->
          (SortedMap Int (List Constant), SortedMap Name StaticPlan)
    add i k (known, ss) = (insert i (k :: fromMaybe [] (lookup i known)) known, note k ss)

    mutual
      go : List VMInst -> (SortedMap Int (List Constant), SortedMap Name StaticPlan) ->
           (SortedMap Int (List Constant), SortedMap Name StaticPlan)
      go [] acc = acc
      go (i :: is) acc = go is (one i acc)

      one : VMInst -> (SortedMap Int (List Constant), SortedMap Name StaticPlan) ->
            (SortedMap Int (List Constant), SortedMap Name StaticPlan)
      one (MKCONSTANT r k) acc@(known, ss) = case key r of
        Just i => add i k acc
        Nothing => (known, note k ss)
      one (MKCON _ (Left c) []) (known, ss) = (known, insert (nullaryCon c) (Nullary c) ss)
      one (OP r (Cast _ to) [x]) acc@(known, ss) =
        let folded = mapMaybe (\k => intConst k >>= (castConstant to . snd))
                              (fromMaybe [] (key x >>= \i => lookup i known))
        in case key r of
             Just i => foldl (\a, f => add i f a) acc folded
             Nothing => (known, foldl (flip note) ss folded)
      -- lint: allow trust-escape: VMCode nests its instruction lists in tuples, which totality checking does not see through
      one (CASE _ alts d) acc = assert_total (maybe id go d (foldl (\a, alt => go (snd alt) a) acc alts))
      one (CONSTCASE _ alts d) acc = assert_total (maybe id go d (foldl (\a, alt => go (snd alt) a) acc alts))
      one _ acc = acc

||| Each function and static of the declarations by name, with its variable.
record Refs (enc : Enc) (d : Decls enc) where
  constructor MkRefs
  funs : SortedMap Name (s ** Var d.sigs s)
  stats : SortedMap Name (s ** Var d.statics s)

refsOf : (d : Decls enc) -> Refs enc d
refsOf d = MkRefs (fromList [(s.name, (s ** v)) | (s ** v) <- enumerate d.sigs])
                  (fromList [(s.sym, (s ** v)) | (s ** v) <- enumerate d.statics])

------------------------------------------------------------------------------
-- Locals

||| What a local holds: an operand, and the constant it is, if known, so that
||| a cast of it is done while compiling.
Env : (Ty enc -> Type) -> Type
Env v = SortedMap Int (Opnd v Val, Maybe Constant)

-- The registers a list of instructions writes, and those it reads, nested
-- alternatives included. `union x y` inserts the elements of `y` into `x`,
-- so each union here takes the smaller set second: the other way, a list's
-- set is built again at every instruction, the square of its length.
mutual
  writes : List VMInst -> SortedSet Int
  writes [] = empty
  writes (i :: is) = union (writes is) (writes1 i)

  writes1 : VMInst -> SortedSet Int
  -- lint: allow trust-escape: VMCode nests its instruction lists in tuples, which totality checking does not see through
  writes1 (CASE _ alts d) = assert_total (union (altsWrite alts) (maybe empty writes d))
  writes1 (CONSTCASE _ alts d) = assert_total (union (altsWrite alts) (maybe empty writes d))
  writes1 i = maybe empty singleton (target i >>= key)

  altsWrite : List (a, List VMInst) -> SortedSet Int
  altsWrite [] = empty
  altsWrite ((_, is) :: as) = union (altsWrite as) (writes is)

  target : VMInst -> Maybe Reg
  target (ASSIGN d _) = Just d
  target (MKCON d _ _) = Just d
  target (MKCLOSURE d _ _ _) = Just d
  target (MKCONSTANT d _) = Just d
  target (APPLY d _ _) = Just d
  target (CALL d _ _ _) = Just d
  target (OP d _ _) = Just d
  target (EXTPRIM d _ _) = Just d
  target (PROJECT d _ _) = Just d
  target (NULL d) = Just d
  target _ = Nothing

mutual
  reads : List VMInst -> SortedSet Int
  reads [] = empty
  reads (i :: is) = union (reads is) (reads1 i)

  reads1 : VMInst -> SortedSet Int
  reads1 (ASSIGN _ s) = regs [s]
  reads1 (MKCON _ _ as) = regs as
  reads1 (MKCLOSURE _ _ _ as) = regs as
  reads1 (APPLY _ f a) = regs [f, a]
  reads1 (CALL _ _ _ as) = regs as
  reads1 (OP _ _ as) = regs (toList as)
  reads1 (EXTPRIM _ _ as) = regs as
  -- lint: allow trust-escape: VMCode nests its instruction lists in tuples, which totality checking does not see through
  reads1 (CASE s alts d) = assert_total (union (union (altsRead alts) (maybe empty reads d)) (regs [s]))
  reads1 (CONSTCASE s alts d) = assert_total (union (union (altsRead alts) (maybe empty reads d)) (regs [s]))
  reads1 (PROJECT _ v _) = regs [v]
  reads1 _ = empty

  altsRead : List (a, List VMInst) -> SortedSet Int
  altsRead [] = empty
  altsRead ((_, is) :: as) = union (altsRead as) (reads is)

  regs : List Reg -> SortedSet Int
  regs rs = fromList (mapMaybe key rs)

||| Each instruction with what is read after it, given what is read after
||| the list: one pass, from the end, so that a case does not compute what
||| the code after it reads again, which made a function of n cases cost the
||| cube of n.
annotate : SortedSet Int -> List VMInst -> List (VMInst, SortedSet Int)
annotate later is = snd (go is)
  where
    go : List VMInst -> (SortedSet Int, List (VMInst, SortedSet Int))
    go [] = (later, [])
    go (i :: is) = let (r, ais) = go is in (union r (reads1 i), (i, r) :: ais)

isRVal : Reg -> Bool
isRVal RVal = True
isRVal _ = False

get : Env v -> Reg -> Opnd v Val
get env r = maybe Erased fst (key r >>= \k => lookup k env)

known : Env v -> Reg -> Maybe Constant
known env r = key r >>= \k => lookup k env >>= snd

set : Env v -> Reg -> Opnd v Val -> Env v
set env r x = maybe env (\k => insert k (x, Nothing) env) (key r)

setKnown : Env v -> Reg -> Opnd v Val -> Constant -> Env v
setKnown env r x c = maybe env (\k => insert k (x, Just c) env) (key r)

||| Operands of `Val`s for parameters of `Val`s.
vals : (xs : List (Opnd v Val)) -> All (Opnd v) (replicate (length xs) Val)
vals [] = []
vals (x :: xs) = x :: vals xs

||| Each element with its position.
numbered : List a -> List (Nat, a)
numbered = go 0
  where
    go : Nat -> List a -> List (Nat, a)
    go _ [] = []
    go i (x :: xs) = (i, x) :: go (S i) xs

allVals : {n : Nat} -> All (Opnd v) (replicate n Val) -> List (Opnd v Val)
allVals {n = Z} [] = []
allVals {n = S n} (x :: xs) = x :: allVals xs

parameters {enc : Enc} {auto 0 fx : HasFixnums enc.val}
           (0 d : Decls enc) (refs : Refs enc d)
           {0 v : Ty enc -> Type} {0 l : List (Ty enc) -> Type}

  0 B : Type -> Type
  B = Build d InCPS False v l

  0 E : Type
  E = End d InCPS False v l

  ||| A fixnum as an immediate `Val`, its range decided here.
  fixnum : Integer -> Maybe (Opnd v Val)
  fixnum i = let w : Int64 = cast i in
    if cast w /= i then Nothing else case choose (inFixnumRange (cast w)) of
      Left ok => Just (Vx {enc} w)
      Right _ => Nothing

  ||| A word as an immediate.
  word : Integer -> Opnd v W64
  word i = W (cast i)

  ------------------------------------------------------------------------------
  -- References

  ||| A runtime routine's variable, with its results and parameters.
  routine : Name -> (rs, ps : List (Ty enc)) -> Maybe (n ** Var d.sigs (MkSig n (InDirect rs False) ps False))
  routine name rs ps = case lookup name refs.funs of
    Just (MkSig n (InDirect rs' False) ps' False ** var) => case (decEq rs' rs, decEq ps' ps) of
      (Yes Refl, Yes Refl) => Just (n ** var)
      _ => Nothing
    _ => Nothing

  ||| A call of a runtime routine, binding its results.
  callRoutine : Name -> {rs : List (Ty enc)} -> {ps : List (Ty enc)} -> All (Opnd v) ps -> B (All (Opnd v) rs)
  callRoutine name xs = case routine name rs ps of
    Just (_ ** r) => directCall r xs
    Nothing => crash ("no runtime routine " ++ show name)

  ||| A call of a string routine of the program's encoding.
  strings : String -> {rs : List (Ty enc)} -> {ps : List (Ty enc)} -> All (Opnd v) ps -> B (All (Opnd v) rs)
  strings op xs = callRoutine (stringRoutine enc op) xs

  ||| A word known to be in the fixnum range, as a value: a count or a code
  ||| point.
  wordFix : Opnd v W64 -> B (Opnd v Val)
  wordFix w = do f <- emit1 (Tag w); emit1 (WidenFix f)

  ||| A comparison of strings: the runtime's order, -1, 0 or 1, against 0.
  stringOrder : Rel -> Opnd v Val -> Opnd v Val -> B (Opnd v Val)
  stringOrder rel x y = do
    [o] <- strings "compare" {rs = [W64]} {ps = [Val, Val]} [x, y]
    b <- emit1 (Cmp rel o (W 0))
    wordFix b

  ||| An `Integer` routine that makes an `Integer`.
  integerCall : String -> (xs : List (Opnd v Val)) -> B (Opnd v Val)
  integerCall what xs = case xs of
    [x] => do [r] <- callRoutine (integerRoutine what) {rs = [Val]} {ps = [Val]} [x]; pure r
    [x, y] => do [r] <- callRoutine (integerRoutine what) {rs = [Val]} {ps = [Val, Val]} [x, y]; pure r
    _ => crash ("the Integer routine " ++ what ++ " takes one or two values")

  ||| A CPS function of the program of `n` parameters.
  cpsFunction : Name -> (n : Nat) -> Maybe (nm ** cv ** Var d.sigs (MkSig nm InCPS (replicate n Val) cv))
  cpsFunction name n = case lookup name refs.funs of
    Just (MkSig nm InCPS ps cv ** var) => case decEq ps (replicate n Val) of
      Yes Refl => Just (nm ** cv ** var)
      No _ => Nothing
    _ => Nothing

  ||| A static object of the program, as a `Val`.
  staticVal : Name -> B (Opnd v Val)
  staticVal name = case lookup name refs.stats of
    Just (MkStaticSig _ _ ** var) => do p <- emit1 (StaticAddr var); emit1 (WidenPtr p)
    Nothing => unsupported ("the static object " ++ show name ++ ", which no declaration makes")

  ------------------------------------------------------------------------------
  -- Integer values

  -- An immediate needs no instruction to change type: a fixnum is the
  -- same integer as a `Val`, a `Fix` or a word.

  ||| A uniform value known to be a fixnum, as a `Fix`.
  asFix : Opnd v Val -> B (Opnd v Fix)
  asFix (Vx {ok} i) = pure (Fx {ok} i)
  asFix Erased = pure (Fx 0)
  asFix x = emit1 (NarrowFix x)

  ||| A fixnum's value, as a word.
  untag : Opnd v Fix -> B (Opnd v W64)
  untag (Fx i) = pure (W i)
  untag f = emit1 (Untag f)

  fixValue : Opnd v Val -> B (Opnd v W64)
  fixValue x = asFix x >>= untag

  widen : Opnd v Fix -> B (Opnd v Val)
  widen (Fx {ok} i) = pure (Vx {enc} {ok} i)
  widen f = emit1 (WidenFix f)

  ||| The pattern an `INT64` box holds.
  boxWord : Opnd v Val -> B (Opnd v W64)
  boxWord x = do
    p <- emit1 (NarrowPtr INT64 x)
    emit1 (Load W64 (MkMem (AtPtr p) Nothing 8))

  ||| A 64-bit integer's pattern: untagged from a fixnum, loaded from a box.
  wideWord : Opnd v Val -> B (Opnd v W64)
  wideWord (Vx i) = pure (W i)
  wideWord Erased = pure (W 0)
  wideWord x = do
    [w] <- joinPoint [W64] $ \done =>
      ifFixnums [x] (\[f] => do w <- untag (f); done [w]) (do w <- boxWord x; done [w])
    pure w

  ||| A 64-bit pattern as a uniform value: tagged if its signed value is in the
  ||| fixnum range, boxed otherwise.
  wideVal : Opnd v W64 -> B (Opnd v Val)
  wideVal w = do
    [r] <- joinPoint [Val] $ \done =>
      tagOv w (\f => do r <- widen f; done [r])
              (do p <- emit1 (AllocObj Int64H [w]); r <- emit1 (WidenPtr p); done [r])
    pure r

  ||| A word wrapped to a narrow width, as a uniform value: a fixnum, which it
  ||| always fits.
  narrowVal : Nat -> Bool -> Opnd v W64 -> B (Opnd v Val)
  narrowVal n s w = do
    e <- emit1 (Ext (subWord n) s w)
    f <- emit1 (Tag e)
    widen f

  ||| A comparison's 0 or 1, as the `Int` Idris's comparisons give.
  boolVal : Opnd v W64 -> B (Opnd v Val)
  boolVal c = emit1 (Tag c) >>= widen

  ||| An `Integer`'s value modulo 2^64, as a word.
  integerBits : Opnd v Val -> B (Opnd v W64)
  integerBits x = do
    [w] <- joinPoint [W64] $ \done =>
      ifFixnums [x] (\[f] => do w <- untag (f); done [w])
        (do [w] <- callRoutine (integerRoutine "to_bits64") {rs = [W64]} {ps = [Val]} [x]; done [w])
    pure w

  ------------------------------------------------------------------------------
  -- Integer operations

  ||| The overflow form of an operation that has one.
  ovOp : ArithOp -> Maybe OvOp
  ovOp Add = Just OvAdd
  ovOp Sub = Just OvSub
  ovOp Mul = Just OvMul
  ovOp _ = Nothing

  ||| Addition, subtraction, multiplication and the bitwise operations; the
  ||| name is the operation's `Integer` routine.
  arithmetic : IntWidth -> ArithOp -> (routine : String) -> (x, y : Opnd v Val) -> B (Opnd v Val)
  arithmetic (Narrow n s) o _ x y = do
    a <- fixValue x
    b <- fixValue y
    w <- emit1 (Arith o a b)
    narrowVal n s w
  arithmetic (Wide _) o _ x y = do
    [r] <- joinPoint [Val] $ \done => do
      words <- block [W64, W64] $ \[wa, wb] => do
        w <- emit1 (Arith o wa wb)
        r <- wideVal w
        done [r]
      ifFixnums [x, y]
        (\[a, b] => case ovOp o of
           Just ov => arithOv ov a b (\f => do r <- widen f; done [r])
                        (do wa <- untag (a); wb <- untag (b); words [wa, wb])
           Nothing => do f <- emit1 (Arith o a b); r <- widen f; done [r])
        (do wa <- wideWord x; wb <- wideWord y; words [wa, wb])
    pure r
  arithmetic Unbounded o routine x y = do
    [r] <- joinPoint [Val] $ \done => do
      slow <- block [] $ \[] => do r <- integerCall routine [x, y]; done [r]
      ifFixnums [x, y]
        (\[a, b] => case ovOp o of
           Just ov => arithOv ov a b (\f => do r <- widen f; done [r]) (slow [])
           Nothing => do f <- emit1 (Arith o a b); r <- widen f; done [r])
        (slow [])
    pure r

  negation : IntWidth -> Opnd v Val -> B (Opnd v Val)
  negation (Narrow n s) x = do
    a <- fixValue x
    w <- emit1 (Unary Negate a)
    narrowVal n s w
  negation (Wide _) x = do
    [r] <- joinPoint [Val] $ \done => do
      word <- block [W64] $ \[wa] => do
        w <- emit1 (Unary Negate wa)
        r <- wideVal w
        done [r]
      ifFixnums [x]
        (\[a] => arithOv OvSub (Fx 0) a (\f => do r <- widen f; done [r])
                   (do wa <- untag (a); word [wa]))
        (do wa <- wideWord x; word [wa])
    pure r
  negation Unbounded x = do
    [r] <- joinPoint [Val] $ \done => do
      slow <- block [] $ \[] => do r <- integerCall "neg" [x]; done [r]
      ifFixnums [x] (\[a] => arithOv OvSub (Fx 0) a (\f => do r <- widen f; done [r]) (slow [])) (slow [])
    pure r

  ||| `div` or `mod`.
  division : IntWidth -> (remainder : Bool) -> (x, y : Opnd v Val) -> B (Opnd v Val)
  division (Narrow n s) m x y = do
    a <- fixValue x
    b <- fixValue y
    nonZero b
    w <- divide s m a b
    narrowVal n s w
  division (Wide s) m x y = do
    a <- wideWord x
    b <- wideWord y
    nonZero b
    w <- divide s m a b
    wideVal w
  division Unbounded m x y = do
    [r] <- joinPoint [Val] $ \done => do
      slow <- block [] $ \[] => do r <- integerCall (if m then "mod" else "div") [x, y]; done [r]
      ifFixnums [x, y]
        (\[fa, fb] => do
           a <- untag (fa)
           b <- untag (fb)
           branch EqR b (W 0) (slow []) $ do
             w <- divide True m a b
             tagOv w (\f => do r <- widen f; done [r]) (slow []))
        (slow [])
    pure r

  ||| `shiftL` or `shiftR`: arithmetic on signed types, logical on unsigned.
  shifting : IntWidth -> (left : Bool) -> (x, y : Opnd v Val) -> B (Opnd v Val)
  shifting (Narrow n s) left x y = do
    a <- fixValue x
    k <- fixValue y
    w <- shiftBy (if left then Shl else if s then Sar else Shr) a k
    narrowVal n s w
  shifting (Wide s) left x y = do
    a <- wideWord x
    k <- wideWord y
    w <- shiftBy (if left then Shl else if s then Sar else Shr) a k
    wideVal w
  shifting Unbounded left x y = do
    [r] <- joinPoint [Val] $ \done => do
      slow <- block [] $ \[] => do r <- integerCall (if left then "shl" else "shr") [x, y]; done [r]
      ifFixnums [x, y]
        (\[fa, fk] => do
           a <- untag (fa)
           k <- untag (fk)
           branch LtS k (W 0) (slow []) $
             if left
                then -- shift by at most 62, and keep the result only if
                     -- shifting back gives the operand and it is a fixnum
                     branch GtS k (W 62) (slow []) $ do
                       w <- emit1 (Arith Shl a k)
                       back <- emit1 (Arith Sar w k)
                       branch NeR back a (slow []) $
                         tagOv w (\f => do r <- widen f; done [r]) (slow [])
                else do
                  w <- shiftBy Sar a k
                  f <- emit1 (Tag w)
                  r <- widen f
                  done [r])
        (slow [])
    pure r

  ||| A comparison, giving the `Int` 0 or 1.
  comparison : IntWidth -> Rel -> (x, y : Opnd v Val) -> B (Opnd v Val)
  comparison (Narrow _ _) rel x y = do
    a <- asFix x
    b <- asFix y
    c <- emit1 (Cmp rel a b)
    boolVal c
  comparison (Wide s) rel x y = do
    let rel' = if s then rel else unsignedRel rel
    [c] <- joinPoint [W64] $ \done =>
      ifFixnums [x, y]
        (\[a, b] => do c <- emit1 (Cmp rel' a b); done [c])
        (do a <- wideWord x; b <- wideWord y; c <- emit1 (Cmp rel' a b); done [c])
    boolVal c
  comparison Unbounded rel x y = do
    [c] <- joinPoint [W64] $ \done =>
      ifFixnums [x, y]
        (\[a, b] => do c <- emit1 (Cmp rel a b); done [c])
        (do [o] <- callRoutine (integerRoutine "compare") {rs = [W64]} {ps = [Val, Val]} [x, y]
            c <- emit1 (Cmp rel o (W 0))
            done [c])
    boolVal c

  ||| A cast to `Char`: the value if it is a Unicode scalar value, 0 if not.
  toChar : IntWidth -> Opnd v Val -> B (Opnd v Val)
  toChar wf x = do
    w <- case wf of
      Narrow _ _ => fixValue x
      Wide _ => wideWord x
      Unbounded => do
        [w] <- joinPoint [W64] $ \done =>
          ifFixnums [x] (\[f] => do w <- untag (f); done [w]) (done [W (-1)])
        pure w
    [r] <- joinPoint [Val] $ \done => do
      keep <- block [] $ \[] => do f <- emit1 (Tag w); r <- widen f; done [r]
      zero <- block [] $ \[] => done [Vx {enc} 0]
      branch LtS w (W 0) (zero []) $
        branch LeS w (W 55295) (keep []) $
          branch LtS w (W 57344) (zero []) $
            branch LeS w (W 1114111) (keep []) (zero [])
    pure r

  ||| A uniform integer of one width as one of another, wrapping as Idris's
  ||| casts do.
  retype : IntWidth -> IntWidth -> Opnd v Val -> B (Opnd v Val)
  retype wf wt x =
    if keeps wf wt then pure x else case (wf, wt) of
      (Narrow _ _, Narrow n s) => fixValue x >>= narrowVal n s
      (Wide _, Narrow n s) => wideWord x >>= narrowVal n s
      (Unbounded, Narrow n s) => integerBits x >>= narrowVal n s
      (Unbounded, Wide _) => do
        [r] <- joinPoint [Val] $ \done =>
          ifFixnums [x] (\_ => done [x]) (do a <- integerBits x; r <- wideVal a; done [r])
        pure r
      (Wide True, Unbounded) => do
        [r] <- joinPoint [Val] $ \done =>
          ifFixnums [x] (\_ => done [x])
            (do a <- boxWord x
                [r] <- callRoutine (integerRoutine "from_int64") {rs = [Val]} {ps = [W64]} [a]
                done [r])
        pure r
      (Wide False, Unbounded) => do
        a <- wideWord x
        [r] <- joinPoint [Val] $ \done =>
          branch LtU a (W 4611686018427387904)
            (do f <- emit1 (Tag a); r <- widen f; done [r])
            (do [r] <- callRoutine (integerRoutine "from_bits64") {rs = [Val]} {ps = [W64]} [a]; done [r])
        pure r
      _ => pure x

  ||| A constant: an integer is an immediate when it is a fixnum, and the
  ||| static object that holds it otherwise.
  constant : Constant -> B (Opnd v Val)
  constant WorldVal = pure Erased
  constant (PrT _) = pure Erased
  constant (Str s) = staticVal (stringStatic s)
  constant (Db _) = unsupported "a double constant"
  constant k = case intConst k of
    Just (Wide _, n) => let p = patternValue n in maybe (staticVal (int64Static p)) pure (fixnum p)
    Just (Unbounded, n) =>
      maybe (case signInHeader enc.bignum of
               Just _ => staticVal (bignumStatic n)
               Nothing => unsupported "an Integer constant outside the fixnum range, under bignums in two's complement")
            pure (fixnum n)
    Just (Narrow _ _, n) => maybe (unsupported ("the constant " ++ show k)) pure (fixnum n)
    Nothing => unsupported ("the constant " ++ show k)

  withWidth : PrimType -> String -> (IntWidth -> B a) -> B a
  withWidth ty what k = case intWidth ty of
    Just w => k w
    Nothing => unsupported (what ++ " on " ++ show ty)

  ||| A primitive operation, and the environment after it.
  op : Env v -> Reg -> PrimFn n -> Vect n Reg -> B (Env v)
  op env r (Cast from to) [x] = case (intWidth from, intWidth to) of
    (Just wf, Just wt) => case known env x >>= intConst >>= (castConstant to . snd) of
      Just folded => do c <- constant folded; pure (setKnown env r c folded)
      Nothing => do
        c <- if to == CharType then toChar wf (get env x) else retype wf wt (get env x)
        pure (set env r c)
    _ => unsupported ("the cast from " ++ show from ++ " to " ++ show to)
  op env r BelieveMe [_, _, x] = pure (set env r (get env x))
  op env r fn args = set env r <$> value fn args
    where
      value : PrimFn m -> Vect m Reg -> B (Opnd v Val)
      value (Add ty) [x, y] = withWidth ty "addition" (\w => arithmetic w Add "add" (get env x) (get env y))
      value (Sub ty) [x, y] = withWidth ty "subtraction" (\w => arithmetic w Sub "sub" (get env x) (get env y))
      value (Mul ty) [x, y] = withWidth ty "multiplication" (\w => arithmetic w Mul "mul" (get env x) (get env y))
      value (Div ty) [x, y] = withWidth ty "division" (\w => division w False (get env x) (get env y))
      value (Mod ty) [x, y] = withWidth ty "remainder" (\w => division w True (get env x) (get env y))
      value (Neg ty) [x] = withWidth ty "negation" (\w => negation w (get env x))
      value (ShiftL ty) [x, y] = withWidth ty "a left shift" (\w => shifting w True (get env x) (get env y))
      value (ShiftR ty) [x, y] = withWidth ty "a right shift" (\w => shifting w False (get env x) (get env y))
      value (BAnd ty) [x, y] = withWidth ty "bitwise and" (\w => arithmetic w And "and" (get env x) (get env y))
      value (BOr ty) [x, y] = withWidth ty "bitwise or" (\w => arithmetic w Or "or" (get env x) (get env y))
      value (BXOr ty) [x, y] = withWidth ty "bitwise xor" (\w => arithmetic w Xor "xor" (get env x) (get env y))
      -- the string primitives: the runtime's routines under the encoding
      value StrLength [s] = do [n] <- strings "length" {rs = [W64]} {ps = [Val]} [get env s]; wordFix n
      value StrHead [s] = do [c] <- strings "head" {rs = [W64]} {ps = [Val]} [get env s]; wordFix c
      value StrTail [s] = do [r] <- strings "tail" {rs = [Val]} {ps = [Val]} [get env s]; pure r
      value StrIndex [s, i] = do
        w <- wideWord (get env i)
        [c] <- strings "index" {rs = [W64]} {ps = [Val, W64]} [get env s, w]
        wordFix c
      value StrCons [c, s] = do
        w <- fixValue (get env c)
        [r] <- strings "cons" {rs = [Val]} {ps = [W64, Val]} [w, get env s]
        pure r
      value StrAppend [a, b] = do [r] <- strings "append" {rs = [Val]} {ps = [Val, Val]} [get env a, get env b]; pure r
      value StrReverse [s] = do [r] <- strings "reverse" {rs = [Val]} {ps = [Val]} [get env s]; pure r
      value StrSubstr [o, l, s] = do
        wo <- wideWord (get env o)
        wl <- wideWord (get env l)
        [r] <- strings "substr" {rs = [Val]} {ps = [W64, W64, Val]} [wo, wl, get env s]
        pure r
      value (LT StringType) [x, y] = stringOrder LtS (get env x) (get env y)
      value (LTE StringType) [x, y] = stringOrder LeS (get env x) (get env y)
      value (EQ StringType) [x, y] = stringOrder EqR (get env x) (get env y)
      value (GTE StringType) [x, y] = stringOrder GeS (get env x) (get env y)
      value (GT StringType) [x, y] = stringOrder GtS (get env x) (get env y)
      value (LT ty) [x, y] = withWidth ty "<" (\w => comparison w LtS (get env x) (get env y))
      value (LTE ty) [x, y] = withWidth ty "<=" (\w => comparison w LeS (get env x) (get env y))
      value (EQ ty) [x, y] = withWidth ty "==" (\w => comparison w EqR (get env x) (get env y))
      value (GTE ty) [x, y] = withWidth ty ">=" (\w => comparison w GeS (get env x) (get env y))
      value (GT ty) [x, y] = withWidth ty ">" (\w => comparison w GtS (get env x) (get env y))
      value fn _ = unsupported ("the primitive " ++ show fn)

  ------------------------------------------------------------------------------
  -- Arrays
  --
  -- The `%extern` primitives of `Data.IOArray.Prims`, on `ARRAY` objects. Each
  -- takes the erased element type first and the world last. An index or a
  -- size is an `Int`, read as its 64-bit pattern; `AllocSized` refuses a
  -- size its header cannot hold, a negative one included. The bounds of a
  -- read or a write are the caller's to check, as on every backend:
  -- `Data.IOArray` checks them. Writing an element needs no barrier while the
  -- collector is not generational.

  extPrim : Env v -> Reg -> Name -> List Reg -> B (Env v)
  extPrim env r p [_, x, y, _] =
    if p == arrayPrim "prim__newArray"
       then do count <- wideWord (get env x)
               a <- emit1 (AllocSized ArrayElems count (get env y))
               set env r <$> emit1 (WidenPtr a)
    else if p == arrayPrim "prim__arrayGet"
       then do a <- emit1 (NarrowPtr ARRAY (get env x))
               i <- wideWord (get env y)
               set env r <$> emit1 (Load Val (MkMem (AtPtr a) (Just i) 8))
    else unsupported ("the external primitive " ++ show p)
  -- The result is `()`, which no caller inspects: the erased value.
  extPrim env r p [_, x, y, z, _] =
    if p == arrayPrim "prim__arraySet"
       then do a <- emit1 (NarrowPtr ARRAY (get env x))
               i <- wideWord (get env y)
               emit0 (Store Val (MkMem (AtPtr a) (Just i) 8) (get env z))
               pure (set env r Erased)
    else unsupported ("the external primitive " ++ show p)
  extPrim env r p _ = unsupported ("the external primitive " ++ show p)

  ------------------------------------------------------------------------------
  -- Objects

  ||| A constructor object, its header's fit decided here.
  constructor : Int -> (fields : List (Opnd v Val)) -> B (Opnd v Val)
  constructor conId fields = case choose (wellFormed (ConH {enc} (cast conId) (length fields))) of
    Left ok => do
      p <- emit1 (AllocObj (ConH (cast conId) (length fields)) (vals fields))
      emit1 (WidenPtr p)
    Right _ => unsupported ("the constructor id " ++ show conId ++ ", which its header cannot hold")

  ||| A closure of the function, with the arguments filled and `missing` to
  ||| come, its header decided here.
  closure : Name -> Var d.sigs (MkSig n InCPS ps cv) -> (missing : Nat) -> (args : List (Opnd v Val)) -> B (Opnd v Val)
  closure f code missing args =
    case choose (wellFormed (ClosureH {enc} (missing + length args) (length args))) of
      Left ok => do
        c <- emit1 (CodeAddr code)
        p <- emit1 (AllocObj (ClosureH (missing + length args) (length args)) (c :: vals args))
        emit1 (WidenPtr p)
      Right _ => unsupported ("a closure of " ++ show f ++ " that its header cannot hold")

  ------------------------------------------------------------------------------
  -- The boundary with flat code
  --
  -- A function that has a flat form (`Compiler.Native.LowerFlat`) is a
  -- wrapper around the form's `Direct` function: it takes its arguments
  -- apart into the form's registers, calls the form, and builds its result
  -- from the form's, as ordinary code represents each type
  -- (`Flat.Exp.Ordinary`).

  isTag : ConShape -> Bool
  isTag c = case c.ordinary of
    AsTag => True
    _ => False

  mutual
    ||| The registers of an ordinary value of the shape.
    unbox : Shape -> Opnd v Val -> B (Value enc v)
    unbox (PrimShape DoubleType) x = do
      p <- emit1 (NarrowPtr DOUBLE x)
      f <- emit1 (Load F64 (MkMem (AtPtr p) Nothing 8))
      pure (MkValue [Dbl] [f])
    unbox (PrimShape WorldType) _ = pure noRegs
    unbox (PrimShape t) x = case intWidth t of
      Just (Narrow _ _) => do w <- fixValue x; pure (MkValue [Word] [w])
      Just (Wide _) => do w <- wideWord x; pure (MkValue [Word] [w])
      _ => unsupported ("a value of " ++ show t ++ " passed to flat code")
    unbox UniformShape x = pure (MkValue [Uniform] [x])
    unbox (DataShape []) _ = pure noRegs
    unbox (DataShape [c]) x = concatValues <$> fieldsFrom c x
    unbox s@(DataShape cs) x =
      if all isTag cs then do t <- fixValue x; pure (MkValue [Word] [t]) else do
        let lay = shapeLayout s
        q <- emit1 (NarrowPtr CON x)
        i <- emit1 (LoadPart ConId q)
        rs <- joinPoint (tys lay) $ \done => do
          let branches = mapMaybe (\c => case (c.ordinary, placement cs c.name) of
                                           (AsObject cid, Just (_, p)) => Just (the Int64 (cast cid), do
                                             fs <- fieldsFrom c x
                                             r <- conValue p (concatValues fs)
                                             maybe (unsupported "a sum of another layout") done (regsAs lay r))
                                           _ => Nothing) cs
          if length branches /= length cs then unsupported "a sum some of whose constructors are not objects" else
            case choose (distinct (map fst branches) && keysFit (W64 {enc}) (map fst branches)) of
              Left ok => switch i branches (crash "no constructor of the type")
              Right _ => unsupported "a sum with repeated constructor ids"
        pure (MkValue lay rs)

    ||| The registers of the fields of an ordinary value of the constructor.
    fieldsFrom : ConShape -> Opnd v Val -> B (List (Value enc v))
    fieldsFrom c x = case c.ordinary of
      AsTag => pure []
      -- the newtype's other fields, such as `MkIORes`'s world, take no
      -- registers
      AsField k => traverse (\(j, s) => unbox s (if j == k then x else Erased)) (numbered c.fields)
      AsObject _ => case c.fields of
        [] => pure []
        fs => do
          q <- emit1 (NarrowPtr CON x)
          traverse (\(j, s) => do f <- emit1 (Load Val (MkMem (AtPtr q) Nothing (8 + 8 * cast j)))
                                  unbox s f)
                   (numbered fs)

  mutual
    ||| The ordinary value of the shape, from its registers.
    box : Shape -> Value enc v -> B (Opnd v Val)
    box (PrimShape DoubleType) x = case doubleOf x of
      Just f => do p <- emit1 (AllocObj DoubleH [f]); emit1 (WidenPtr p)
      Nothing => unsupported "a double of another layout from flat code"
    box (PrimShape WorldType) _ = pure Erased
    box (PrimShape t) x = case (intWidth t, wordOf x) of
      (Just (Narrow _ _), Just w) => do f <- emit1 (Tag w); widen f
      (Just (Wide _), Just w) => wideVal w
      _ => unsupported ("a value of " ++ show t ++ " returned by flat code")
    box UniformShape x = case x of
      MkValue [Uniform] [u] => pure u
      _ => unsupported "a uniform value of another layout from flat code"
    box (DataShape []) _ = pure Erased
    box (DataShape [c]) x = boxCon c x
    box (DataShape cs) x = case tagOf x of
      Nothing => unsupported "a sum without its tag from flat code"
      Just t => if all isTag cs then do f <- emit1 (Tag t); widen f else do
        [r] <- joinPoint [Val] $ \done => do
          let branches = mapMaybe (\c => do (_, p) <- placement cs c.name
                                            fs <- fieldsOf p x
                                            pure (the Int64 (cast c.tag), do r <- boxCon c fs; done [r])) cs
          if length branches /= length cs then unsupported "a sum of another layout from flat code" else
            case choose (distinct (map fst branches) && keysFit (W64 {enc}) (map fst branches)) of
              Left ok => switch t branches (crash "no constructor of the type")
              Right _ => unsupported "a sum with repeated tags"
        pure r

    ||| The ordinary value of the constructor, from its fields' registers.
    boxCon : ConShape -> Value enc v -> B (Opnd v Val)
    boxCon c fs = case splitBy (map shapeLayout c.fields) fs of
      Nothing => unsupported ("the fields of " ++ show c.name ++ ", of another layout")
      Just xs => case c.ordinary of
        AsTag => maybe (unsupported "a tag outside the fixnum range") pure (fixnum (cast c.tag))
        AsField k => case getAt k (zip c.fields xs) of
          Just (s, f) => box s f
          Nothing => unsupported ("the newtype " ++ show c.name ++ " without its field")
        AsObject cid => case c.fields of
          [] => staticVal (nullaryCon cid)
          _ => do ys <- traverse (uncurry box) (zip c.fields xs); constructor cid ys

  ||| A function that has a flat form: its arguments taken apart, the form
  ||| called, its result built.
  boundary : Callee d -> (params : List Shape) -> (result : Shape) -> List (Opnd v Val) -> E
  boundary (MkCallee fd (_ ** var)) ss rs xs = do
    parts <- traverse (uncurry unbox) (zip ss xs)
    case regsAs (paramsLayout fd.params) (concatValues parts) of
      Nothing => unsupported ("arguments of other layouts for the flat form of " ++ show fd.name)
      Just args => do
        res <- directCall var args
        r <- box rs (MkValue fd.result res)
        return r

  ------------------------------------------------------------------------------
  -- Instructions

  mutual
    ||| The alternatives of a case, as code, and the code after the case,
    ||| from the environment: in tail position each alternative returns
    ||| itself; otherwise they meet at a join whose parameters are the locals
    ||| they assign that the rest reads, and the rest is lowered once.
    ||| `dispatch` branches to the alternatives and the default.
    ||| `after` is what the code after the case reads.
    cases : Env v -> (after : SortedSet Int) -> (tail : Bool) -> List (VMInst, SortedSet Int) -> (Env v -> E) ->
            (alts : List (List VMInst)) -> (dflt : List VMInst) -> (List E -> E -> E) -> E
    cases env after True [] k alts dflt dispatch =
      dispatch (map (\alt => lower env True (annotate after alt) k) alts) (lower env True (annotate after dflt) k)
    cases env after t is k alts dflt dispatch = do
      -- the locals the alternatives assign that the rest reads: each of the
      -- few assigned looked up in what is read after, which is as long as the
      -- rest of the function (`intersection` walks its second set)
      let ks = filter (\r => contains r after)
                      (Prelude.toList (foldr (\alt, w => union w (writes alt)) (writes dflt) alts))
          kset = fromList ks
          exitWith : Jumper d InCPS False v l (replicate (length ks) Val) -> Env v -> E
          exitWith exit e = exit (passed e ks)
      vals <- joinPoint (replicate (length ks) Val) $ \exit =>
        dispatch (map (\alt => lower env False (annotate kset alt) (exitWith exit)) alts)
                 (lower env False (annotate kset dflt) (exitWith exit))
      lower (foldl (\e, (k', x) => insert k' (x, Nothing) e) env (zip ks (allVals vals))) t is k
      where
        -- A local an alternative leaves as it was passes on as it was; one it
        -- never had passes on as the erased value, which no path reads.
        passed : Env v -> (ks : List Int) -> All (Opnd v) (replicate (length ks) Val)
        passed e [] = []
        passed e (k' :: ks') = maybe Erased fst (lookup k' e) :: passed e ks'

    ||| The instructions, each with what is read after it (`annotate`), then
    ||| the rest, `k`, on the environment they leave; in `tail` position the
    ||| rest returns the result.
    lower : Env v -> (tail : Bool) -> List (VMInst, SortedSet Int) -> (Env v -> E) -> E
    lower env t [] k = k env
    lower env t ((DECLARE _, _) :: is) k = lower env t is k
    lower env t ((START, _) :: is) k = lower env t is k
    lower env t ((ASSIGN Discard _, _) :: is) k = lower env t is k
    lower env t ((ASSIGN r x, _) :: is) k = lower (set env r (get env x)) t is k
    lower env t ((NULL r, _) :: is) k = lower (set env r Erased) t is k
    lower env t ((MKCONSTANT r c, _) :: is) k = do
      x <- constant c
      lower (setKnown env r x c) t is k
    lower env t ((MKCON r (Left conId) [], _) :: is) k = do
      x <- staticVal (nullaryCon conId)
      lower (set env r x) t is k
    lower env t ((MKCON r (Left conId) args, _) :: is) k = do
      x <- constructor conId (map (get env) args)
      lower (set env r x) t is k
    lower env t ((MKCON r (Right n) _, _) :: is) k = unsupported ("the type constructor " ++ show n ++ " as a value")
    lower env t ((MKCLOSURE r f missing args, _) :: is) k =
      case lookup f refs.funs of
        Just (MkSig _ InCPS _ _ ** code) => do
          x <- closure f code missing (map (get env) args)
          lower (set env r x) t is k
        _ => unsupported ("a closure of " ++ show f ++ ", which is not a function of the program")
    lower env t ((APPLY r f a, _) :: is) k =
      if t && isNil is && isRVal r
         then tailApply (get env f) (get env a)
         else do
           x <- apply (get env f) (get env a)
           lower (set env r x) t is k
    lower env t ((CALL r tl f args, _) :: is) k =
      case cpsFunction f (length (map (get env) args)) of
        Nothing => unsupported ("a call to " ++ show f ++ ", which is not a function of the program")
        Just (_ ** _ ** callee) =>
          if tl
             then tailCall callee (vals (map (get env) args))
             else do
               x <- call callee (vals (map (get env) args))
               lower (set env r x) t is k
    lower env t ((OP r fn args, _) :: is) k = do
      env' <- op env r fn args
      lower env' t is k
    lower env t ((EXTPRIM r p args, _) :: is) k = do
      env' <- extPrim env r p args
      lower env' t is k
    lower env t ((CASE s alts dflt, after) :: is) k =
      case traverse (either Just (const Nothing) . fst) alts of
        Nothing => unsupported "a case on type constructors"
        Just ids => do
          q <- emit1 (NarrowPtr CON (get env s))
          i <- emit1 (LoadPart ConId q)
          cases env after t is k (map snd alts) (fromMaybe [ERROR "no case alternative matched"] dflt) $
            \codes, other => onKeys i (zip (map cast ids) codes) other
    lower env t ((CONSTCASE s alts dflt, after) :: is) k =
      case traverse (intConst . fst) alts of
        Nothing => unsupported "a case on strings or doubles"
        Just ks =>
          cases env after t is k (map snd alts) (fromMaybe [ERROR "no case alternative matched"] dflt) $
            \codes, other => constCase (get env s) (zip (map snd ks) codes) (map fst (head' ks)) other
    lower env t ((PROJECT r x i, _) :: is) k = do
      q <- emit1 (NarrowPtr CON (get env x))
      f <- emit1 (Load Val (MkMem (AtPtr q) Nothing (8 + 8 * i)))
      lower (set env r f) t is k
    lower env t ((ERROR msg, _) :: _) k = crash msg

    ||| A switch on a word, its keys' distinctness decided here.
    onKeys : Opnd v W64 -> List (Int64, E) -> E -> E
    onKeys x cs other = case choose (distinct (map fst cs) && keysFit (W64 {enc}) (map fst cs)) of
      Left ok => switch x cs other
      Right _ => unsupported "a case with repeated constructor ids"

    ||| A switch on a fixnum, its keys decided here to be distinct fixnums.
    onFixnums : Opnd v Fix -> List (Int64, E) -> E -> E
    onFixnums x cs other = case choose (distinct (map fst cs) && keysFit (Fix {enc}) (map fst cs)) of
      Left ok => switch x cs other
      Right _ => unsupported "a case with repeated constants"

    ||| A case on integer or character constants. A 64-bit scrutinee is
    ||| matched as a fixnum against the cases in the fixnum range and as a box
    ||| against the others; an `Integer` that is a `BIGNUM` matches no case in
    ||| the fixnum range.
    constCase : Opnd v Val -> List (Integer, E) -> Maybe IntWidth -> E -> E
    constCase x cs (Just (Wide _)) other = do
      -- each alternative is reached from both switches, so it is a block
      alts <- traverse (\(n, code) => do j <- block [] (\[] => code); pure (patternValue n, j)) cs
      dflt <- block [] (\[] => other)
      ifFixnums [x]
        (\[f] => onFixnums f [(cast p, j []) | (p, j) <- alts, inFixnumRange p] (dflt []))
        (case [(cast p, j []) | (p, j) <- alts, not (inFixnumRange p)] of
           [] => dflt []
           big => do w <- boxWord x; onKeys w big (dflt []))
    constCase x cs (Just Unbounded) other = do
      dflt <- block [] (\[] => other)
      ifFixnums [x]
        (\[f] => onFixnums f [(cast n, code) | (n, code) <- cs, inFixnumRange n] (dflt []))
        (if all (inFixnumRange . fst) cs
            then dflt []
            else unsupported "a case on an Integer constant outside the fixnum range")
    constCase x cs _ other = do
      f <- asFix x
      onFixnums f [(cast n, code) | (n, code) <- cs] other

------------------------------------------------------------------------------
-- The program

||| What a function of the program is lowered from.
data Plan
  = ||| A VMCode function.
    FromVM (List Int) (List VMInst)
  | ||| A function that has a flat form, of the arity: a wrapper around the
    ||| form's `Direct` function, with the shapes of its parameters and of its
    ||| result.
    Boundary Nat FlatDef (List Shape) Shape
  | ||| A flat form: its `Direct` function.
    Form FlatDef
  | ||| A foreign function, of the arity.
    Foreign Nat
  | ||| A routine of the runtime.
    Routine
  | ||| The entry, when the program has none.
    NoEntry

parameters {enc : Enc} {auto 0 fx : HasFixnums enc.val}
  ||| A VMCode function: its parameters are its locals at entry, and it
  ||| returns its result register.
  lowerFunction : (d : Decls enc) -> Refs enc d -> (args : List Int) -> List VMInst ->
                  Closed d InCPS False (replicate (length args) Val)
  lowerFunction d refs args body = build $ \ps =>
    lower d refs (fromList (zip args (map (\x => (x, Nothing)) (allVals ps)))) True (annotate (singleton (-1)) body)
          (\env => return (get env RVal))

  ||| A foreign function the runtime does not implement: the abort stub.
  lowerForeign : (d : Decls enc) -> Refs enc d -> Name -> (arity : Nat) -> Closed d InCPS False (replicate arity Val)
  lowerForeign d refs n arity = build $ \ps => unsupported ("the foreign function " ++ show n)

  ||| A function that has a flat form, as the wrapper around the form's.
  lowerBoundary : (d : Decls enc) -> Refs enc d -> Callee d -> List Shape -> Shape -> (arity : Nat) ->
                  Closed d InCPS False (replicate arity Val)
  lowerBoundary d refs ce ss r arity = build $ \ps => boundary d refs ce ss r (allVals ps)

  ||| A function's definition, from its plan.
  defOf : (d : Decls enc) -> Refs enc d -> Forms enc d -> (s : Sig enc) -> Plan -> Def d s
  defOf d refs fs (MkSig n InCPS ps False) (FromVM args body) = case decEq ps (replicate (length args) Val) of
    Yes Refl => Defined (fromMaybe (Unsupported "a level outside its context") (close (lowerFunction d refs args body)))
    No _ => Defined (Unsupported ("the parameters of " ++ show n))
  defOf d refs fs (MkSig n InCPS ps False) (Boundary arity fd ss r) =
    case (decEq ps (replicate arity Val), lookup fd.name fs.callees) of
      (Yes Refl, Just ce) =>
        Defined (fromMaybe (Unsupported "a level outside its context") (close (lowerBoundary d refs ce ss r arity)))
      _ => Defined (Unsupported ("the boundary of " ++ show n))
  defOf d refs fs (MkSig n (InDirect rs False) ps cv) (Form fd) =
    case (decEq rs (tys fd.result), decEq ps (tys (paramsLayout fd.params)), decEq cv (convertsIn fd.name)) of
      (Yes Refl, Yes Refl, Yes Refl) => Defined (fromMaybe (Unsupported "a level outside its context") (close (lowerForm d fs fd)))
      _ => Defined (Unsupported ("the registers of the flat form of " ++ show fd.name))
  defOf d refs fs (MkSig n InCPS ps False) (Foreign arity) = case decEq ps (replicate arity Val) of
    Yes Refl => Defined (fromMaybe (Unsupported "a level outside its context") (close (lowerForeign d refs n arity)))
    No _ => Defined (Unsupported ("the parameters of " ++ show n))
  defOf d refs fs (MkSig n (InDirect rs False) ps False) Routine = External
  defOf d refs fs s NoEntry = Defined (Unsupported "a program without __mainExpression")
  defOf d refs fs s _ = Defined (Unsupported ("the definition of " ++ show s.name))

  defs : (d : Decls enc) -> Refs enc d -> Forms enc d -> (es : List (Sig enc, Plan)) -> All (Def d) (map Builtin.fst es)
  defs d refs fs [] = []
  defs d refs fs ((s, p) :: es) = defOf d refs fs s p :: defs d refs fs es

  ||| A static object's declaration and definition, if its header can hold
  ||| it. Its words name nothing, so it is defined for any declarations.
  -- A big constant's static: a header of its sign and words.
  bigStatic : Name -> Integer -> (sh : SignInHeader enc.bignum) -> (ws : List Int64) ->
              Maybe (s ** ({0 d : Decls enc} -> StaticDef d s))
  bigStatic n v sh ws = case choose (wellFormed (BignumH {enc} @{sh} (v < 0) (length ws))) of
    Left ok => Just (MkStaticSig n BIGNUM ** MkStaticDef (BignumH @{sh} (v < 0) (length ws)) (map SWord (fromList ws)))
    Right _ => Nothing

  ready : (Name, StaticPlan) -> Maybe (s ** ({0 d : Decls enc} -> StaticDef d s))
  ready (n, Nullary c) = case choose (wellFormed (ConH {enc} (cast c) 0)) of
    Left ok => Just (MkStaticSig n CON ** MkStaticDef (ConH (cast c) 0) [])
    Right _ => Nothing
  ready (n, Boxed p) = Just (MkStaticSig n INT64 ** MkStaticDef Int64H [SWord (cast p)])
  ready (n, Big v) = case signInHeader enc.bignum of
    Just sh => bigStatic n v sh (magnitudeWords (abs v))
    Nothing => Nothing
  ready (n, Text s) = do
    (h ** ws) <- literal enc s
    case choose (wellFormed h) of
      Left ok => Just (MkStaticSig n STRING ** MkStaticDef h (map SWord ws))
      Right _ => Nothing

  staticDefs : (d : Decls enc) -> (rs : List (s ** ({0 d' : Decls enc} -> StaticDef d' s))) ->
               All (StaticDef d) (map DPair.fst rs)
  staticDefs d [] = []
  staticDefs d ((_ ** def) :: rs) = def :: staticDefs d rs

||| The entry's signature: CPS, of no parameters.
mainSig : Sig enc
mainSig = MkSig mainExpression InCPS [] False

||| The declarations: the entry first, the other functions, the statics.
declsOf : (es : List (Sig enc, Plan)) -> (rs : List (s ** ({0 d : Decls enc} -> StaticDef d s))) -> Decls enc
declsOf es rs = MkDecls (mainSig :: map Builtin.fst es) (map DPair.fst rs)

||| The program of the declarations, the entry first.
program : {enc : Enc} -> {auto 0 fx : HasFixnums enc.val} -> List FlatDef -> Shapes -> SortedMap Name Name -> Plan ->
          (es : List (Sig enc, Plan)) -> (rs : List (s ** ({0 d : Decls enc} -> StaticDef d s))) -> TermProgram enc
program forms shapes services entry es rs =
  case choose (distinct (map (.name) (mainSig :: map Builtin.fst es)) && distinct (map (.sym) (map DPair.fst rs))) of
    Left ok =>
      (declsOf es rs ** MkProgram
                     (defs (declsOf es rs) (refsOf (declsOf es rs)) (MkForms (callees (declsOf es rs) forms) shapes services)
                           ((mainSig, entry) :: es))
                     (staticDefs (declsOf es rs) rs) (MkEntry here) noConIds)
    Right _ =>
      (MkDecls [mainSig] [] ** MkProgram
                     [Defined (Unsupported "a program with two definitions of one name")] [] (MkEntry here) noConIds)

||| The ids of the constructors of no fields that ordinary code represents
||| as objects, in a shape: the statics boxing a value of it may need.
nullaries : Shape -> Builder Int
nullaries (PrimShape _) = neutral
nullaries UniformShape = neutral
nullaries (DataShape cs) = concatMap con cs
  where
    con : ConShape -> Builder Int
    con c = (case (c.ordinary, c.fields) of
               (AsObject cid, []) => single cid
               _ => neutral) <+> concatMap nullaries c.fields

||| Whether a value of the C type is held as a flat value of the skeleton:
||| an integer as its machine type, a `Char`, a `Double`, the world, `()`, a
||| primitive's `IORes`, and a `String` held as ordinary code holds it.
export
cfAgrees : CFType -> Skeleton -> Bool
cfAgrees CFInt (SPrim IntType) = True
cfAgrees CFInt8 (SPrim Int8Type) = True
cfAgrees CFInt16 (SPrim Int16Type) = True
cfAgrees CFInt32 (SPrim Int32Type) = True
cfAgrees CFInt64 (SPrim Int64Type) = True
cfAgrees CFUnsigned8 (SPrim Bits8Type) = True
cfAgrees CFUnsigned16 (SPrim Bits16Type) = True
cfAgrees CFUnsigned32 (SPrim Bits32Type) = True
cfAgrees CFUnsigned64 (SPrim Bits64Type) = True
cfAgrees CFChar (SPrim CharType) = True
cfAgrees CFDouble (SPrim DoubleType) = True
cfAgrees CFWorld (SPrim WorldType) = True
cfAgrees CFUnit (SCon n []) = n == NS (mkNamespace "Builtin") (UN (Basic "Unit"))
cfAgrees (CFIORes t) (SCon n [s]) = n == NS (mkNamespace "PrimIO") (UN (Basic "IORes")) && cfAgrees t s
cfAgrees CFString (SCon n [SPrim StringType]) = n == uniformType
cfAgrees (CFUser t _) (SCon n [SCon t' _]) = n == uniformType && t == t'
cfAgrees _ _ = False

||| A whole program, as a term: every function and foreign function, the
||| runtime's routines, the statics of the nullary constructors and of the
||| big constants, and `__mainExpression` as the entry, first.
|||
||| The flat forms given are those of the program's functions and of what
||| they call, with the shapes of the data types they handle. A function
||| that has a form becomes the boundary to it, if its arity is the form's
||| and the shapes of its parameters and result are known, and every form
||| becomes a `Direct` function.
|||
||| A foreign function the runtime implements (`Compiler.Native.Linkage.
||| foreignFunctions`) becomes the boundary to the runtime's function, which
||| must take and return, position by position, what the foreign function's
||| C types say; one that does not is an error.
|||
||| The runtime's routines are forms among them, each checked against the
||| runtime contract (`Compiler.Native.Linkage.routines`): a routine the
||| runtime has must have a form of the declared signature, or the program
||| is not lowered, and the error says which. One it does not have yet is
||| declared as outside the program. So are the functions that implement
||| the OS services on the platform (`Compiler.Native.Linkage.osServices`),
||| each checked against its service where a form calls it.
export
lowerProgram : (enc : Enc) -> {auto 0 fx : HasFixnums enc.val} -> Platform -> List FlatDef -> Shapes ->
               List (Name, VMDef) -> Either String (TermProgram enc)
lowerProgram enc platform forms shapes vmdefs = do
  traverse_ provided (routines {enc})
  traverse_ implemented (osServices {enc})
  traverse_ agrees (mapMaybe boundForeign vmdefs)
  let entryPlan = case Data.List.lookup mainExpression vmdefs of
                    Just (MkVMFun [] body) => FromVM [] body
                    _ => NoEntry
      planned = mapMaybe plan (filter ((/= mainExpression) . fst) vmdefs)
      others = planned
                 ++ [(formSig fd, Form fd) | fd <- forms]
                 ++ [(MkSig r.name (InDirect r.results False) r.params False, Routine)
                    | r <- routines {enc}, not r.provided]
      boxing = fromList [(nullaryCon c, Nullary c) | c <- contents (concatMap (boxed . snd) planned)]
      statics = Data.SortedMap.toList (foldl mergeLeft boxing (mapMaybe bodyStatics vmdefs))
  pure (program forms shapes (fromList (serviceBindings {enc} platform)) entryPlan others (mapMaybe ready statics))
  where
    -- A service's function, of the service's signature, if a form calls it.
    implemented : OSService enc -> Either String ()
    implemented s = case serviceFunction platform s of
      Nothing => Left ("the platform " ++ show platform ++ " has no OS services")
      Just f => case find (\fd => fd.name == f) forms of
        Nothing => Right ()
        Just fd =>
          let rs = tys {enc} fd.result
              ps = tys {enc} (paramsLayout fd.params)
          in if rs == s.results && ps == s.params then Right ()
             else Left (show f ++ ", the service " ++ s.service ++ " on " ++ show platform
                        ++ ", has the signature " ++ show ps ++ " -> " ++ show rs
                        ++ ", but the runtime calls it as " ++ show s.params ++ " -> " ++ show s.results)

    -- A routine the runtime has: its form, of the declared signature.
    provided : Routine enc -> Either String ()
    provided r =
      if not r.provided then Right () else
      case find (\fd => fd.name == r.name) forms of
        Nothing => Left ("the runtime has no routine " ++ show r.name ++ ", which generated code calls")
        Just fd =>
          let rs = tys {enc} fd.result
              ps = tys {enc} (paramsLayout fd.params)
          in if rs == r.results && ps == r.params then Right ()
             else Left ("the runtime's " ++ show r.name ++ " has the signature "
                        ++ show ps ++ " -> " ++ show rs
                        ++ ", but generated code calls it as "
                        ++ show r.params ++ " -> " ++ show r.results)

    byName : SortedMap Name FlatDef
    byName = fromList [(fd.name, fd) | fd <- forms]

    boundForeign : (Name, VMDef) -> Maybe (Name, List CFType, CFType)
    boundForeign (n, MkVMForeign _ fargs ret) = if elem n (map fst (foreignFunctions enc)) then Just (n, fargs, ret) else Nothing
    boundForeign _ = Nothing

    -- A foreign function and its implementation, position by position.
    agrees : (Name, List CFType, CFType) -> Either String ()
    agrees (n, fargs, ret) = case Data.List.lookup n (foreignFunctions enc) >>= \f => lookup f byName of
      Nothing => Left ("the runtime has no function that implements " ++ show n)
      Just fd =>
        if length fd.params == length fargs
           && all (\(c, p) => cfAgrees c p.skeleton) (zip fargs fd.params)
           && cfAgrees ret fd.resultSkeleton
           then Right ()
           else Left (show fd.name ++ " takes " ++ show (map skeleton fd.params)
                      ++ " and returns " ++ show fd.resultSkeleton ++ ", but " ++ show n
                      ++ " is declared with " ++ show fargs ++ " -> " ++ show ret)

    -- The boundary of a function that has a form of its arity, whose
    -- parameters' and result's shapes are known and lay out as the form's.
    -- A foreign function's is its implementation's.
    boundaryOf : Name -> Nat -> Maybe Plan
    boundaryOf n arity = do
      fd <- lookup n byName <|> (Data.List.lookup n (foreignFunctions enc) >>= \f => lookup f byName)
      guard (length fd.params == arity)
      ss <- traverse (shapeOf shapes . skeleton) fd.params
      r <- shapeOf shapes fd.resultSkeleton
      guard (map shapeLayout ss == map layout fd.params && shapeLayout r == fd.result)
      pure (Boundary arity fd ss r)

    -- The nullary constructors a boundary may box.
    boxed : Plan -> Builder Int
    boxed (Boundary _ _ ss r) = concatMap nullaries (r :: ss)
    boxed _ = neutral

    plan : (Name, VMDef) -> Maybe (Sig enc, Plan)
    plan (n, MkVMFun args body) =
      Just (MkSig n InCPS (replicate (length args) Val) False,
            fromMaybe (FromVM args body) (boundaryOf n (length args)))
    plan (n, MkVMForeign _ fargs _) =
      Just (MkSig n InCPS (replicate (length fargs) Val) False,
            fromMaybe (Foreign (length fargs)) (boundaryOf n (length fargs)))
    plan (n, MkVMError _) = Nothing

    bodyStatics : (Name, VMDef) -> Maybe (SortedMap Name StaticPlan)
    bodyStatics (_, MkVMFun _ body) = Just (staticsOf body)
    bodyStatics _ = Nothing
