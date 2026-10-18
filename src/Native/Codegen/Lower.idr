||| The produce pass: VMCode and flat forms to the typed term
||| (`Native.Codegen.TermIR.Program`), from which register allocation
||| (`Native.Codegen.RegAlloc`) makes the located IR.
|||
||| Every VMCode function becomes a `CPS` function of `Val` parameters,
||| written in `Build` (`Native.Codegen.TermIR.Build`), so Idris
||| checks its scoping and types when this module is compiled. VMCode's
||| locals are mutable; the term's values are not. The locals are therefore
||| an environment, from each local to the operand it holds, threaded through
||| the lowering: an `ASSIGN` is no code, and a constant is an immediate. A
||| `CASE` or `CONSTCASE` is a join point whose parameters are the locals its
||| alternatives assign and the code after it reads, so that code is lowered
||| once; in tail position the alternatives return directly. A non-tail call
||| or application has the rest of the code as its continuation. What is
||| live where is computed when the term becomes IR (`Native.Codegen.RegAlloc`).
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
||| the casts of integers and characters to strings, an `Integer` in the
||| fixnum range; constructors, nullary ones as shared statics; closures;
||| application; calls and tail calls; cases on constructors, on integer and
||| character constants and on string constants; projection; the arrays
||| behind `Data.IOArray` ("Arrays", below) and the references behind
||| `Data.IORef` ("References"); the string primitives; and the
||| foreign functions the runtime implements. Everything else lowers to
||| `Unsupported`, the abort stub, so a program always links and fails only
||| on the paths it reaches.
|||
||| A function that has a flat form (`Flat.Exp`) is not lowered from its
||| VMCode: the form becomes a `Direct` function (`Native.Codegen.LowerFlat`),
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
module Native.Codegen.Lower

import Native.Codegen.IRCommon.ConIds
import Native.Codegen.IRCommon.Conv
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Codegen.Linkage.ConvertsIn
import Native.Codegen.Linkage.ForeignFunctions
import Native.Codegen.Linkage.Realised as Linkage
import Native.Codegen.Linkage.Routine
import Native.Codegen.LowerFlat
import Native.Codegen.Platform
import Native.Codegen.Strings
import Native.Codegen.TermIR.Body as TermIR
import Native.Codegen.TermIR.Build as TermIR
import Native.Codegen.TermIR.Decls as TermIR
import Native.Codegen.TermIR.Def as TermIR
import Native.Codegen.TermIR.FieldTys
import Native.Codegen.TermIR.Instr
import Native.Codegen.TermIR.IsInt
import Native.Codegen.TermIR.Mem as TermIR
import Native.Codegen.TermIR.Opnd as TermIR
import Native.Codegen.TermIR.OvOp as TermIR
import Native.Codegen.TermIR.Program as TermIR
import Native.Codegen.TermIR.Sig as TermIR
import Native.Codegen.TermIR.Sizes
import Native.Codegen.TermIR.StaticDef as TermIR
import Native.Codegen.TermIR.StaticSig as TermIR
import Native.Codegen.TermIR.Var as TermIR
import Native.Codegen.Words

import Compiler.VMCode
import Core.CompileExpr
import Core.Name
import Core.Name.Namespace
import Core.TT.Primitive
import Data.List
import Data.List.Quantifiers
import Data.Maybe
import Data.So
import Data.SortedMap
import Data.SortedSet
import Data.Vect
import Data.Zippable
import Decidable.Equality
import Decidable.Equality.Core
import Native.Data.Builder as Data
import Native.Data.Distinct
import Native.Flat.Exp
import Native.HeapObj.Shape as HeapObj
import Native.HeapObj.ValEnc
import Native.Port
import Native.Types.BignumEnc
import Native.Types.Enc as Types
import Native.Types.Header as Types
import Native.Types.IntegerRoutine as Types
import Native.Types.Kind
import Native.Types.StringRoutine as Types

%default covering


------------------------------------------------------------------------------
-- Names the lowering introduces

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

||| Each function and static of the declarations by name, with its variable,
||| and the contract as the loaded runtime realises it.
record Refs (enc : Types.Enc) (d : TermIR.Decls enc) where
  constructor MkRefs
  funs : SortedMap Name (s ** TermIR.Var d.sigs s)
  stats : SortedMap Name (s ** TermIR.Var d.statics s)
  realised : Linkage.Realised

------------------------------------------------------------------------------
-- Locals

||| What a local holds: an operand, and the constant it is, if known, so that
||| a cast of it is done while compiling.
Env : (IRCommon.Ty enc -> Type) -> Type
Env v = SortedMap Int (TermIR.Opnd v IRCommon.Ty.Val, Maybe Constant)

||| Each instruction with what is read after it, given what is read after
||| the list: one pass, from the end, so that a case does not compute what
||| the code after it reads again, which made a function of n cases cost the
||| cube of n.
annotate : SortedSet Int -> List VMInst -> List (VMInst, SortedSet Int)
annotate later is = snd (go is)
  where
    reads1 : VMInst -> SortedSet Int
    reads1 inst = case inst of
      ASSIGN _ s => regs [s]
      MKCON _ _ as => regs as
      MKCLOSURE _ _ _ as => regs as
      APPLY _ f a => regs [f, a]
      CALL _ _ _ as => regs as
      OP _ _ as => regs (toList as)
      EXTPRIM _ _ as => regs as
      -- lint: allow trust-escape: VMCode nests its instruction lists in tuples, which totality checking does not see through
      CASE s alts d => assert_total (union (union (altsRead alts) (maybe empty reads d)) (regs [s]))
      CONSTCASE s alts d => assert_total (union (union (altsRead alts) (maybe empty reads d)) (regs [s]))
      PROJECT _ v _ => regs [v]
      _ => empty
      where
        reads : List VMInst -> SortedSet Int
        reads [] = empty
        reads (i :: is) = union (reads is) (reads1 i)

        altsRead : List (a, List VMInst) -> SortedSet Int
        altsRead [] = empty
        altsRead ((_, is) :: as) = union (altsRead as) (reads is)

        regs : List Reg -> SortedSet Int
        regs rs = fromList (mapMaybe key rs)

    go : List VMInst -> (SortedSet Int, List (VMInst, SortedSet Int))
    go [] = (later, [])
    go (i :: is) = let (r, ais) = go is in (union r (reads1 i), (i, r) :: ais)

get : Env v -> Reg -> TermIR.Opnd v IRCommon.Ty.Val
get env r = maybe TermIR.Opnd.Erased fst (key r >>= \k => lookup k env)

known : Env v -> Reg -> Maybe Constant
known env r = key r >>= \k => lookup k env >>= snd

||| Operands of `Val`s for parameters of `Val`s.
vals : (xs : List (TermIR.Opnd v IRCommon.Ty.Val)) -> All (TermIR.Opnd v) (replicate (length xs) IRCommon.Ty.Val)
vals [] = []
vals (x :: xs) = x :: vals xs

allVals : {n : Nat} -> All (TermIR.Opnd v) (replicate n IRCommon.Ty.Val) -> List (TermIR.Opnd v IRCommon.Ty.Val)
allVals {n = Z} [] = []
allVals {n = S n} (x :: xs) = x :: allVals xs

parameters {enc : Types.Enc} {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val}
           (0 d : TermIR.Decls enc) (refs : Refs enc d)
           {0 v : IRCommon.Ty enc -> Type} {0 l : List (IRCommon.Ty enc) -> Type}

  0 B : Type -> Type
  B = TermIR.Build d IRCommon.Conv.CPS False v l

  0 E : Type
  E = TermIR.Build.End d IRCommon.Conv.CPS False v l

  ||| A fixnum as an immediate `Val`, its range decided here.
  fixnum : Integer -> Maybe (TermIR.Opnd v IRCommon.Ty.Val)
  fixnum i = let w : Int64 = cast i in
    if cast w /= i then Nothing else case choose (HeapObj.ValEnc.inFixnumRange (cast w)) of
      Left ok => Just (TermIR.Opnd.Vx {enc} w)
      Right _ => Nothing

  ------------------------------------------------------------------------------
  -- References

  ||| A static object of the program, as a `Val`.
  staticVal : Name -> B (TermIR.Opnd v IRCommon.Ty.Val)
  staticVal name = case lookup name refs.stats of
    Just (TermIR.MkStaticSig _ _ ** var) => do p <- TermIR.Build.emit1 (TermIR.Instr.StaticAddr var)
                                               TermIR.Build.emit1 (TermIR.Instr.WidenPtr p)
    Nothing => TermIR.Build.unsupported ("the static object " ++ show name ++ ", which no declaration makes")

  ------------------------------------------------------------------------------
  -- Integer values

  -- An immediate needs no instruction to change type: a fixnum is the
  -- same integer as a `Val`, a `Fix` or a word.

  ||| A uniform value known to be a fixnum, as a `Fix`.
  asFix : TermIR.Opnd v IRCommon.Ty.Val -> B (TermIR.Opnd v IRCommon.Ty.Fix)
  asFix (TermIR.Opnd.Vx {ok} i) = pure (TermIR.Opnd.Fx {ok} i)
  asFix TermIR.Opnd.Erased = pure (TermIR.Opnd.Fx 0)
  asFix x = TermIR.Build.emit1 (TermIR.Instr.NarrowFix x)

  ||| A fixnum's value, as a word.
  untag : TermIR.Opnd v IRCommon.Ty.Fix -> B (TermIR.Opnd v IRCommon.Ty.W64)
  untag (TermIR.Opnd.Fx i) = pure (TermIR.Opnd.W i)
  untag f = TermIR.Build.emit1 (TermIR.Instr.Untag f)

  fixValue : TermIR.Opnd v IRCommon.Ty.Val -> B (TermIR.Opnd v IRCommon.Ty.W64)
  fixValue x = asFix x >>= untag

  widen : TermIR.Opnd v IRCommon.Ty.Fix -> B (TermIR.Opnd v IRCommon.Ty.Val)
  widen (TermIR.Opnd.Fx {ok} i) = pure (TermIR.Opnd.Vx {enc} {ok} i)
  widen f = TermIR.Build.emit1 (TermIR.Instr.WidenFix f)

  ||| The pattern an `INT64` box holds.
  boxWord : TermIR.Opnd v IRCommon.Ty.Val -> B (TermIR.Opnd v IRCommon.Ty.W64)
  boxWord x = do
    p <- TermIR.Build.emit1 (TermIR.Instr.NarrowPtr Types.Kind.INT64 x)
    TermIR.Build.emit1 (TermIR.Instr.Load IRCommon.Ty.W64 (TermIR.MkMem (TermIR.Mem.AtPtr p) Nothing 8))

  ||| A 64-bit integer's pattern: untagged from a fixnum, loaded from a box.
  wideWord : TermIR.Opnd v IRCommon.Ty.Val -> B (TermIR.Opnd v IRCommon.Ty.W64)
  wideWord (TermIR.Opnd.Vx i) = pure (TermIR.Opnd.W i)
  wideWord TermIR.Opnd.Erased = pure (TermIR.Opnd.W 0)
  wideWord x = do
    [w] <- TermIR.Build.joinPoint [IRCommon.Ty.W64] $ \done =>
      TermIR.Build.ifFixnums [x] (\[f] => do w <- untag (f); done [w]) (do w <- boxWord x; done [w])
    pure w

  ||| A 64-bit pattern as a uniform value: tagged if its signed value is in the
  ||| fixnum range, boxed otherwise.
  wideVal : TermIR.Opnd v IRCommon.Ty.W64 -> B (TermIR.Opnd v IRCommon.Ty.Val)
  wideVal w = do
    [r] <- TermIR.Build.joinPoint [IRCommon.Ty.Val] $ \done =>
      TermIR.Build.tagOv w (\f => do r <- widen f; done [r])
              (do p <- TermIR.Build.emit1 (TermIR.Instr.AllocObj Types.Header.Int64H [w])
                  r <- TermIR.Build.emit1 (TermIR.Instr.WidenPtr p)
                  done [r])
    pure r

  ------------------------------------------------------------------------------
  -- Integer operations

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
  --
  -- References
  --
  -- The `%extern` primitives of `Data.IORef`, on `IOREF` objects: the value
  -- at 8. Each takes the erased value type first and the world last. A
  -- write needs no barrier, as an array's does not.

  ------------------------------------------------------------------------------
  -- Objects

  ||| A constructor object, its header's fit decided here.
  constructor : Int -> (fields : List (TermIR.Opnd v IRCommon.Ty.Val)) -> B (TermIR.Opnd v IRCommon.Ty.Val)
  constructor conId fields =
    case choose (TermIR.FieldTys.wellFormed (Types.Header.ConH {enc} (cast conId) (length fields))) of
    Left ok => do
      p <- TermIR.Build.emit1 (TermIR.Instr.AllocObj (Types.Header.ConH (cast conId) (length fields)) (vals fields))
      TermIR.Build.emit1 (TermIR.Instr.WidenPtr p)
    Right _ => TermIR.Build.unsupported ("the constructor id " ++ show conId ++ ", which its header cannot hold")

  ------------------------------------------------------------------------------
  -- The boundary with flat code
  --
  -- A function that has a flat form (`Native.Codegen.LowerFlat`) is a
  -- wrapper around the form's `Direct` function: it takes its arguments
  -- apart into the form's registers, calls the form, and builds its result
  -- from the form's, as ordinary code represents each type
  -- (`Flat.Exp.Ordinary`).

  ||| A function that has a flat form: its arguments taken apart, the form
  ||| called, its result built.
  boundary : LowerFlat.Callee d -> (params : List Flat.Exp.Shape) -> (result : Flat.Exp.Shape) ->
             List (TermIR.Opnd v IRCommon.Ty.Val) -> E
  boundary (LowerFlat.MkCallee fd (_ ** var)) ss rs xs = do
    parts <- traverse (uncurry unbox) (zip ss xs)
    case LowerFlat.regsAs (LowerFlat.paramsLayout fd.params) (LowerFlat.concatValues parts) of
      Nothing => TermIR.Build.unsupported ("arguments of other layouts for the flat form of " ++ show fd.name)
      Just args => do
        res <- TermIR.Build.directCall var args
        r <- box rs (LowerFlat.MkValue fd.result res)
        TermIR.Build.return r
    where
      isTag : Flat.Exp.ConShape -> Bool
      isTag c = case c.ordinary of
        Flat.Exp.AsTag => True
        _ => False

      ||| The registers of an ordinary value of the shape.
      unbox : Flat.Exp.Shape -> TermIR.Opnd v IRCommon.Ty.Val -> B (LowerFlat.Value enc v)
      unbox shape x = case shape of
        Flat.Exp.PrimShape DoubleType => do
                   p <- TermIR.Build.emit1 (TermIR.Instr.NarrowPtr Types.Kind.DOUBLE x)
                   f <- TermIR.Build.emit1
                     (TermIR.Instr.Load IRCommon.Ty.F64 (TermIR.MkMem (TermIR.Mem.AtPtr p) Nothing 8))
                   pure (LowerFlat.MkValue [Flat.Exp.Dbl] [f])
        Flat.Exp.PrimShape WorldType => pure LowerFlat.noRegs
        Flat.Exp.PrimShape t => case intWidth t of
                   Just (Narrow _ _) => do w <- fixValue x; pure (LowerFlat.MkValue [Flat.Exp.Word] [w])
                   Just (Wide _) => do w <- wideWord x; pure (LowerFlat.MkValue [Flat.Exp.Word] [w])
                   _ => TermIR.Build.unsupported ("a value of " ++ show t ++ " passed to flat code")
        Flat.Exp.UniformShape => pure (LowerFlat.MkValue [Flat.Exp.Uniform] [x])
        Flat.Exp.DataShape [] => pure LowerFlat.noRegs
        Flat.Exp.DataShape [c] => LowerFlat.concatValues <$> fieldsFrom c x
        s@(Flat.Exp.DataShape cs) =>
          if all isTag cs then do t <- fixValue x; pure (LowerFlat.MkValue [Flat.Exp.Word] [t]) else do
            let lay = Flat.Exp.shapeLayout s
            q <- TermIR.Build.emit1 (TermIR.Instr.NarrowPtr Types.Kind.CON x)
            i <- TermIR.Build.emit1 (TermIR.Instr.LoadPart Types.Header.ConId q)
            rs <- TermIR.Build.joinPoint (LowerFlat.tys lay) $ \done => do
              let branches = mapMaybe (\c => case (c.ordinary, LowerFlat.placement cs c.name) of
                                               (Flat.Exp.AsObject cid, Just (_, p)) => Just (the Int64 (cast cid), do
                                                          fs <- fieldsFrom c x
                                                          r <- LowerFlat.conValue p (LowerFlat.concatValues fs)
                                                          maybe (TermIR.Build.unsupported "a sum of another layout")
                                                            done (LowerFlat.regsAs lay r))
                                               _ => Nothing) cs
              if length branches /= length cs
                then TermIR.Build.unsupported "a sum some of whose constructors are not objects" else
                case choose
                  (Data.Distinct.distinct (map fst branches)
                   && TermIR.Body.keysFit (IRCommon.Ty.W64 {enc}) (map fst branches)) of
                  Left ok => TermIR.Build.switch i branches (TermIR.Build.crash "no constructor of the type")
                  Right _ => TermIR.Build.unsupported "a sum with repeated constructor ids"
            pure (LowerFlat.MkValue lay rs)
        where
          ||| The registers of the fields of an ordinary value of the constructor.
          fieldsFrom : Flat.Exp.ConShape -> TermIR.Opnd v IRCommon.Ty.Val -> B (List (LowerFlat.Value enc v))
          fieldsFrom c x = case c.ordinary of
            Flat.Exp.AsTag => pure []
            -- the newtype's other fields, such as `MkIORes`'s world, take no
            -- registers
            Flat.Exp.AsField k =>
              traverse (\(j, s) => unbox s (if j == k then x else TermIR.Opnd.Erased)) (numbered c.fields)
            Flat.Exp.AsObject _ => case c.fields of
                       [] => pure []
                       fs => do
                         q <- TermIR.Build.emit1 (TermIR.Instr.NarrowPtr Types.Kind.CON x)
                         traverse (\(j, s) => do f <- TermIR.Build.emit1
                                                   (TermIR.Instr.Load IRCommon.Ty.Val
                                                    (TermIR.MkMem (TermIR.Mem.AtPtr q) Nothing (8 + 8 * cast j)))
                                                 unbox s f)
                                  (numbered fs)
            where
              ||| Each element with its position.
              numbered : List a -> List (Nat, a)
              numbered = go 0
                where
                  go : Nat -> List a -> List (Nat, a)
                  go _ [] = []
                  go i (x :: xs) = (i, x) :: go (S i) xs

      ||| The ordinary value of the shape, from its registers.
      box : Flat.Exp.Shape -> LowerFlat.Value enc v -> B (TermIR.Opnd v IRCommon.Ty.Val)
      box shape x = case shape of
        Flat.Exp.PrimShape DoubleType => case LowerFlat.doubleOf x of
                   Just f => do p <- TermIR.Build.emit1 (TermIR.Instr.AllocObj Types.Header.DoubleH [f])
                                TermIR.Build.emit1 (TermIR.Instr.WidenPtr p)
                   Nothing => TermIR.Build.unsupported "a double of another layout from flat code"
        Flat.Exp.PrimShape WorldType => pure TermIR.Opnd.Erased
        Flat.Exp.PrimShape t => case (intWidth t, LowerFlat.wordOf x) of
                   (Just (Narrow _ _), Just w) => do f <- TermIR.Build.emit1 (TermIR.Instr.Tag w); widen f
                   (Just (Wide _), Just w) => wideVal w
                   _ => TermIR.Build.unsupported ("a value of " ++ show t ++ " returned by flat code")
        Flat.Exp.UniformShape => case x of
                   LowerFlat.MkValue [Flat.Exp.Uniform] [u] => pure u
                   _ => TermIR.Build.unsupported "a uniform value of another layout from flat code"
        Flat.Exp.DataShape [] => pure TermIR.Opnd.Erased
        Flat.Exp.DataShape [c] => boxCon c x
        Flat.Exp.DataShape cs => case LowerFlat.tagOf x of
                   Nothing => TermIR.Build.unsupported "a sum without its tag from flat code"
                   Just t => if all isTag cs then do f <- TermIR.Build.emit1 (TermIR.Instr.Tag t); widen f else do
                     [r] <- TermIR.Build.joinPoint [IRCommon.Ty.Val] $ \done => do
                       let branches = mapMaybe (\c => do (_, p) <- LowerFlat.placement cs c.name
                                                         fs <- LowerFlat.fieldsOf p x
                                                         pure (the Int64 (cast c.tag), do r <- boxCon c fs; done [r]))
                                                           cs
                       if length branches /= length cs
                         then TermIR.Build.unsupported "a sum of another layout from flat code" else
                         case choose
                           (Data.Distinct.distinct (map fst branches)
                            && TermIR.Body.keysFit (IRCommon.Ty.W64 {enc}) (map fst branches)) of
                           Left ok => TermIR.Build.switch t branches (TermIR.Build.crash "no constructor of the type")
                           Right _ => TermIR.Build.unsupported "a sum with repeated tags"
                     pure r
        where
          ||| The ordinary value of the constructor, from its fields' registers.
          boxCon : Flat.Exp.ConShape -> LowerFlat.Value enc v -> B (TermIR.Opnd v IRCommon.Ty.Val)
          boxCon c fs = case LowerFlat.splitBy (map Flat.Exp.shapeLayout c.fields) fs of
            Nothing => TermIR.Build.unsupported ("the fields of " ++ show c.name ++ ", of another layout")
            Just xs => case c.ordinary of
              Flat.Exp.AsTag =>
                maybe (TermIR.Build.unsupported "a tag outside the fixnum range") pure (fixnum (cast c.tag))
              Flat.Exp.AsField k => case getAt k (zip c.fields xs) of
                         Just (s, f) => box s f
                         Nothing => TermIR.Build.unsupported ("the newtype " ++ show c.name ++ " without its field")
              Flat.Exp.AsObject cid => case c.fields of
                         [] => staticVal (nullaryCon cid)
                         _ => do ys <- traverse (uncurry box) (zip c.fields xs); constructor cid ys

  ------------------------------------------------------------------------------
  -- Instructions

  mutual

    ||| The instructions, each with what is read after it (`annotate`), then
    ||| the rest, `k`, on the environment they leave; in `tail` position the
    ||| rest returns the result.
    lower : Env v -> (tail : Bool) -> List (VMInst, SortedSet Int) -> (Env v -> E) -> E
    lower env t list k = case list of
      [] => k env
      (DECLARE _, _) :: is => lower env t is k
      (START, _) :: is => lower env t is k
      (ASSIGN Discard _, _) :: is => lower env t is k
      (ASSIGN r x, _) :: is => lower (set env r (get env x)) t is k
      (NULL r, _) :: is => lower (set env r TermIR.Opnd.Erased) t is k
      (MKCONSTANT r c, _) :: is => do
        x <- constant c
        lower (setKnown env r x c) t is k
      (MKCON r (Left conId) [], _) :: is => do
        x <- staticVal (nullaryCon conId)
        lower (set env r x) t is k
      (MKCON r (Left conId) args, _) :: is => do
        x <- constructor conId (map (get env) args)
        lower (set env r x) t is k
      (MKCON r (Right n) _, _) :: is => TermIR.Build.unsupported ("the type constructor " ++ show n ++ " as a value")
      (MKCLOSURE r f missing args, _) :: is =>
        case lookup f refs.funs of
          Just (TermIR.MkSig _ IRCommon.Conv.CPS _ _ ** code) => do
            x <- closure f code missing (map (get env) args)
            lower (set env r x) t is k
          _ => TermIR.Build.unsupported ("a closure of " ++ show f ++ ", which is not a function of the program")
      (APPLY r f a, _) :: is =>
        if t && isNil is && isRVal r
           then TermIR.Build.tailApply (get env f) (get env a)
           else do
             x <- TermIR.Build.apply (get env f) (get env a)
             lower (set env r x) t is k
      (CALL r tl f args, _) :: is =>
        case cpsFunction f (length (map (get env) args)) of
          Nothing => TermIR.Build.unsupported ("a call to " ++ show f ++ ", which is not a function of the program")
          Just (_ ** _ ** callee) =>
            if tl
               then TermIR.Build.tailCall callee (vals (map (get env) args))
               else do
                 x <- TermIR.Build.call callee (vals (map (get env) args))
                 lower (set env r x) t is k
      (OP r fn args, _) :: is => do
        env' <- op env r fn args
        lower env' t is k
      (EXTPRIM r p args, _) :: is => do
        env' <- extPrim env r p args
        lower env' t is k
      (CASE s alts dflt, after) :: is =>
        case traverse (either Just (const Nothing) . fst) alts of
          Nothing => TermIR.Build.unsupported "a case on type constructors"
          Just ids => do
            q <- TermIR.Build.emit1 (TermIR.Instr.NarrowPtr Types.Kind.CON (get env s))
            i <- TermIR.Build.emit1 (TermIR.Instr.LoadPart Types.Header.ConId q)
            cases env after t is k (map snd alts) (fromMaybe [ERROR "no case alternative matched"] dflt) $
              \codes, other => onKeys i (zip (map cast ids) codes) other
      (CONSTCASE s alts dflt, after) :: is =>
        case (traverse (intConst . fst) alts, traverse (text . fst) alts) of
          (Just ks, _) =>
            cases env after t is k (map snd alts) (fromMaybe [ERROR "no case alternative matched"] dflt) $
              \codes, other => constCase (get env s) (zip (map snd ks) codes) (map fst (head' ks)) other
          (Nothing, Just ts) =>
            cases env after t is k (map snd alts) (fromMaybe [ERROR "no case alternative matched"] dflt) $
              \codes, other => stringCase (get env s) (zip ts codes) other
          (Nothing, Nothing) => TermIR.Build.unsupported "a case on doubles"
      (PROJECT r x i, _) :: is => do
        q <- TermIR.Build.emit1 (TermIR.Instr.NarrowPtr Types.Kind.CON (get env x))
        f <- TermIR.Build.emit1
          (TermIR.Instr.Load IRCommon.Ty.Val (TermIR.MkMem (TermIR.Mem.AtPtr q) Nothing (8 + 8 * i)))
        lower (set env r f) t is k
      (ERROR msg, _) :: _ => TermIR.Build.crash msg
      where
        ||| A closure of the function, with the arguments filled and `missing` to
        ||| come, its header decided here.
        closure : Name -> TermIR.Var d.sigs (TermIR.MkSig n IRCommon.Conv.CPS ps cv) -> (missing : Nat) ->
                  (args : List (TermIR.Opnd v IRCommon.Ty.Val)) -> B (TermIR.Opnd v IRCommon.Ty.Val)
        closure f code missing args =
          case choose
            (TermIR.FieldTys.wellFormed (Types.Header.ClosureH {enc} (missing + length args) (length args))) of
            Left ok => do
              c <- TermIR.Build.emit1 (TermIR.Instr.CodeAddr code)
              p <- TermIR.Build.emit1
                (TermIR.Instr.AllocObj (Types.Header.ClosureH (missing + length args) (length args)) (c :: vals args))
              TermIR.Build.emit1 (TermIR.Instr.WidenPtr p)
            Right _ => TermIR.Build.unsupported ("a closure of " ++ show f ++ " that its header cannot hold")

        isRVal : Reg -> Bool
        isRVal RVal = True
        isRVal _ = False

        ||| A CPS function of the program of `n` parameters.
        cpsFunction : Name -> (n : Nat) ->
                      Maybe
                      (nm ** cv ** TermIR.Var d.sigs
                       (TermIR.MkSig nm IRCommon.Conv.CPS (replicate n IRCommon.Ty.Val) cv))
        cpsFunction name n = case lookup name refs.funs of
          Just (TermIR.MkSig nm IRCommon.Conv.CPS ps cv ** var) => case decEq ps (replicate n IRCommon.Ty.Val) of
            Yes Refl => Just (nm ** cv ** var)
            No _ => Nothing
          _ => Nothing

        set : Env v -> Reg -> TermIR.Opnd v IRCommon.Ty.Val -> Env v
        set env r x = maybe env (\k => insert k (x, Nothing) env) (key r)

        extPrim : Env v -> Reg -> Name -> List Reg -> B (Env v)
        extPrim env r p list =
          if p == arrayPrim "prim__newArray" then case list of
            [_, x, y, _] => do count <- wideWord (get env x)
                               a <- TermIR.Build.emit1 (TermIR.Instr.AllocSized Types.Header.ArrayElems count (get env y))
                               set env r <$> TermIR.Build.emit1 (TermIR.Instr.WidenPtr a)
            _ => notLowered
          else if p == arrayPrim "prim__arrayGet" then case list of
            [_, x, y, _] => do a <- TermIR.Build.emit1 (TermIR.Instr.NarrowPtr Types.Kind.ARRAY (get env x))
                               i <- wideWord (get env y)
                               set env r <$> TermIR.Build.emit1
                                 (TermIR.Instr.Load IRCommon.Ty.Val (TermIR.MkMem (TermIR.Mem.AtPtr a) (Just i) 8))
            _ => notLowered
          -- The result is `()`, which no caller inspects: the erased value.
          else if p == arrayPrim "prim__arraySet" then case list of
            [_, x, y, z, _] => do a <- TermIR.Build.emit1 (TermIR.Instr.NarrowPtr Types.Kind.ARRAY (get env x))
                                  i <- wideWord (get env y)
                                  TermIR.Build.emit0
                                    (TermIR.Instr.Store IRCommon.Ty.Val (TermIR.MkMem (TermIR.Mem.AtPtr a) (Just i) 8)
                                     (get env z))
                                  pure (set env r TermIR.Opnd.Erased)
            _ => notLowered
          else if p == refPrim "prim__newIORef" then case list of
            [_, x, _] => do a <- TermIR.Build.emit1 (TermIR.Instr.AllocObj Types.Header.IORefH [get env x])
                            set env r <$> TermIR.Build.emit1 (TermIR.Instr.WidenPtr a)
            _ => notLowered
          else if p == refPrim "prim__readIORef" then case list of
            [_, x, _] => do a <- TermIR.Build.emit1 (TermIR.Instr.NarrowPtr Types.Kind.IOREF (get env x))
                            set env r <$> TermIR.Build.emit1
                              (TermIR.Instr.Load IRCommon.Ty.Val (TermIR.MkMem (TermIR.Mem.AtPtr a) Nothing 8))
            _ => notLowered
          -- The result is `()`, as an array's write's.
          else if p == refPrim "prim__writeIORef" then case list of
            [_, x, y, _] => do a <- TermIR.Build.emit1 (TermIR.Instr.NarrowPtr Types.Kind.IOREF (get env x))
                               TermIR.Build.emit0
                                 (TermIR.Instr.Store IRCommon.Ty.Val (TermIR.MkMem (TermIR.Mem.AtPtr a) Nothing 8) (get env y))
                               pure (set env r TermIR.Opnd.Erased)
            _ => notLowered
          else notLowered
          where
            notLowered : B (Env v)
            notLowered = TermIR.Build.unsupported ("the external primitive " ++ show p)

            ||| One of the `%extern` array primitives of `Data.IOArray.Prims`.
            arrayPrim : String -> Name
            arrayPrim s = NS (mkNamespace "Data.IOArray.Prims") (UN (Basic s))

            ||| One of the `%extern` primitives of `Data.IORef`.
            refPrim : String -> Name
            refPrim s = NS (mkNamespace "Data.IORef") (UN (Basic s))

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
              exitWith : TermIR.Build.Jumper d IRCommon.Conv.CPS False v l (replicate (length ks) IRCommon.Ty.Val) ->
                         Env v -> E
              exitWith exit e = exit (passed e ks)
          vals <- TermIR.Build.joinPoint (replicate (length ks) IRCommon.Ty.Val) $ \exit =>
            dispatch (map (\alt => lower env False (annotate kset alt) (exitWith exit)) alts)
                     (lower env False (annotate kset dflt) (exitWith exit))
          lower (foldl (\e, (k', x) => insert k' (x, Nothing) e) env (zip ks (allVals vals))) t is k
          where
            -- A local an alternative leaves as it was passes on as it was; one it
            -- never had passes on as the erased value, which no path reads.
            passed : Env v -> (ks : List Int) -> All (TermIR.Opnd v) (replicate (length ks) IRCommon.Ty.Val)
            passed e [] = []
            passed e (k' :: ks') = maybe TermIR.Opnd.Erased fst (lookup k' e) :: passed e ks'

            -- The registers a list of instructions writes, and those it reads, nested
            -- alternatives included. `union x y` inserts the elements of `y` into `x`,
            -- so each union here takes the smaller set second: the other way, a list's
            -- set is built again at every instruction, the square of its length.
            writes : List VMInst -> SortedSet Int
            writes [] = empty
            writes (i :: is) = union (writes is) (writes1 i)
              where
                writes1 : VMInst -> SortedSet Int
                -- lint: allow trust-escape: VMCode nests its instruction lists in tuples, which totality checking does not see through
                writes1 inst = case inst of
                  CASE _ alts d => assert_total (union (altsWrite alts) (maybe empty writes d))
                  CONSTCASE _ alts d => assert_total (union (altsWrite alts) (maybe empty writes d))
                  i => maybe empty singleton (target i >>= key)
                  where
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

                    altsWrite : List (a, List VMInst) -> SortedSet Int
                    altsWrite [] = empty
                    altsWrite ((_, is) :: as) = union (altsWrite as) (writes is)

        ||| A switch on a word, its keys' distinctness decided here.
        onKeys : TermIR.Opnd v IRCommon.Ty.W64 -> List (Int64, E) -> E -> E
        onKeys x cs other =
          case choose
            (Data.Distinct.distinct (map fst cs) && TermIR.Body.keysFit (IRCommon.Ty.W64 {enc}) (map fst cs)) of
          Left ok => TermIR.Build.switch x cs other
          Right _ => TermIR.Build.unsupported "a case with repeated constructor ids"

        ||| A runtime routine's variable, with its results and parameters.
        routine : Name -> (rs, ps : List (IRCommon.Ty enc)) ->
                  Maybe (n' ** TermIR.Var d.sigs (TermIR.MkSig n' (IRCommon.Conv.Direct rs False) ps False))
        routine name rs ps = case lookup name refs.funs of
          Just (TermIR.MkSig n (IRCommon.Conv.Direct rs' False) ps' False ** var) =>
            case (decEq rs' rs, decEq ps' ps) of
            (Yes Refl, Yes Refl) => Just (n ** var)
            _ => Nothing
          _ => Nothing

        ||| A call of a runtime routine, binding its results.
        callRoutine : Name -> {rs : List (IRCommon.Ty enc)} -> {ps : List (IRCommon.Ty enc)} ->
                      All (TermIR.Opnd v) ps -> B (All (TermIR.Opnd v) rs)
        callRoutine name xs = case routine name rs ps of
          Just (_ ** r) => TermIR.Build.directCall r xs
          Nothing => TermIR.Build.crash ("no runtime routine " ++ show name)

        ||| A call of a string routine of the program's encoding, of its port's
        ||| registers.
        strings : (c : Types.StringRoutine) -> All (TermIR.Opnd v) (Linkage.Routine.portParams (Types.StringRoutine.port c)) ->
                  B (All (TermIR.Opnd v) (Linkage.Routine.portResults (Types.StringRoutine.port c)))
        strings c xs = case Linkage.Routine.stringRoutine refs.realised c of
          Just n => callRoutine n xs
          Nothing => TermIR.Build.unsupported "a string operation, which the runtime has no module for under the encoding"

        ||| A call of an `Integer` routine of the program's encoding, of its port's
        ||| registers.
        integers : (c : Types.IntegerRoutine) ->
                   All (TermIR.Opnd v) (Linkage.Routine.portParams (Types.IntegerRoutine.port c)) ->
                   B (All (TermIR.Opnd v) (Linkage.Routine.portResults (Types.IntegerRoutine.port c)))
        integers c xs = case Linkage.Routine.integerRoutine refs.realised c of
          Just n => callRoutine n xs
          Nothing => TermIR.Build.unsupported "an Integer operation beyond the fixnums, which the runtime has none of yet"

        ||| A case on integer or character constants. A 64-bit scrutinee is
        ||| matched as a fixnum against the cases in the fixnum range and as a box
        ||| against the others; an `Integer` that is a `BIGNUM` matches no case in
        ||| the fixnum range.
        constCase : TermIR.Opnd v IRCommon.Ty.Val -> List (Integer, E) -> Maybe IntWidth -> E -> E
        constCase x cs y other = case y of
          Just (Wide _) => do
            -- each alternative is reached from both switches, so it is a block
            alts <- traverse (\(n, code) => do j <- TermIR.Build.block [] (\[] => code); pure (patternValue n, j)) cs
            dflt <- TermIR.Build.block [] (\[] => other)
            TermIR.Build.ifFixnums [x]
              (\[f] => onFixnums f [(cast p, j []) | (p, j) <- alts, HeapObj.ValEnc.inFixnumRange p] (dflt []))
              (case [(cast p, j []) | (p, j) <- alts, not (HeapObj.ValEnc.inFixnumRange p)] of
                 [] => dflt []
                 big => do w <- boxWord x; onKeys w big (dflt []))
          Just Unbounded => do
            dflt <- TermIR.Build.block [] (\[] => other)
            TermIR.Build.ifFixnums [x]
              (\[f] => onFixnums f [(cast n, code) | (n, code) <- cs, HeapObj.ValEnc.inFixnumRange n] (dflt []))
              (if all (HeapObj.ValEnc.inFixnumRange . fst) cs
                  then dflt []
                  else TermIR.Build.unsupported "a case on an Integer constant outside the fixnum range")
          _ => do
            f <- asFix x
            onFixnums f [(cast n, code) | (n, code) <- cs] other
          where
            ||| A switch on a fixnum, its keys decided here to be distinct fixnums.
            onFixnums : TermIR.Opnd v IRCommon.Ty.Fix -> List (Int64, E) -> E -> E
            onFixnums x cs other =
              case choose
                (Data.Distinct.distinct (map fst cs) && TermIR.Body.keysFit (IRCommon.Ty.Fix {enc}) (map fst cs)) of
              Left ok => TermIR.Build.switch x cs other
              Right _ => TermIR.Build.unsupported "a case with repeated constants"

        setKnown : Env v -> Reg -> TermIR.Opnd v IRCommon.Ty.Val -> Constant -> Env v
        setKnown env r x c = maybe env (\k => insert k (x, Just c) env) (key r)

        ||| A constant: an integer is an immediate when it is a fixnum, and the
        ||| static object that holds it otherwise.
        constant : Constant -> B (TermIR.Opnd v IRCommon.Ty.Val)
        constant WorldVal = pure TermIR.Opnd.Erased
        constant (PrT _) = pure TermIR.Opnd.Erased
        constant (Str s) = staticVal (stringStatic s)
        constant (Db _) = TermIR.Build.unsupported "a double constant"
        constant k = case intConst k of
          Just (Wide _, n) => let p = patternValue n in maybe (staticVal (int64Static p)) pure (fixnum p)
          Just (Unbounded, n) =>
            maybe (case Types.BignumEnc.signInHeader enc.bignum of
                     Just _ => staticVal (bignumStatic n)
                     Nothing =>
                       TermIR.Build.unsupported
                         "an Integer constant outside the fixnum range, under bignums in two's complement")
                  pure (fixnum n)
          Just (Narrow _ _, n) => maybe (TermIR.Build.unsupported ("the constant " ++ show k)) pure (fixnum n)
          Nothing => TermIR.Build.unsupported ("the constant " ++ show k)

        ||| A string constant's text.
        text : Constant -> Maybe String
        text (Str x) = Just x
        text _ = Nothing

        ||| A case on string constants: each compared with the value in turn, by
        ||| the string routines' order, the first that is equal taken.
        stringCase : TermIR.Opnd v IRCommon.Ty.Val -> List (String, E) -> E -> E
        stringCase x [] other = other
        stringCase x ((lit, code) :: cs) other = do
          l <- constant (Str lit)
          [o] <- strings Types.StringRoutine.Compare [x, l]
          TermIR.Build.branch IRCommon.Op.EqR o (TermIR.Opnd.W 0) code (stringCase x cs other)

        ||| A primitive operation, and the environment after it.
        op : Env v -> Reg -> PrimFn n -> Vect n Reg -> B (Env v)
        op env r fn' vect = case (fn', vect) of
          (Cast from to, [x]) => case (intWidth from, intWidth to) of
            (Just wf, Just wt) => case known env x >>= intConst >>= (castConstant to . snd) of
              Just folded => do c <- constant folded; pure (setKnown env r c folded)
              Nothing => do
                c <- if to == CharType then toChar wf (get env x) else retype wf wt (get env x)
                pure (set env r c)
            -- a character as a string of it, a number as its decimal text
            (Just wf, Nothing) =>
              if to /= StringType then TermIR.Build.unsupported ("the cast from " ++ show from ++ " to " ++ show to)
              else if from == CharType then do
                w <- fixValue (get env x)
                empty <- constant (Str "")
                [c] <- strings Types.StringRoutine.Cons [w, empty]
                pure (set env r c)
              else set env r <$> decimal wf (get env x)
            -- a string as the integer it reads as, wrapped to the width as a cast
            -- from Integer is
            (Nothing, Just wt) =>
              if from /= StringType || to == CharType
                 then TermIR.Build.unsupported ("the cast from " ++ show from ++ " to " ++ show to)
                 else do
                   [w] <- strings Types.StringRoutine.ReadWord [get env x]
                   c <- case wt of
                     Narrow n s => narrowVal n s w
                     Wide _ => wideVal w
                     Unbounded => TermIR.Build.unsupported "an Integer read from a string, beyond what the runtime's Integer holds yet"
                   pure (set env r c)
            -- a double as its shortest decimal text, and a string as a double
            (Nothing, Nothing) =>
              if from == DoubleType && to == StringType then do
                p <- TermIR.Build.emit1 (TermIR.Instr.NarrowPtr Types.Kind.DOUBLE (get env x))
                f <- TermIR.Build.emit1 (TermIR.Instr.Load IRCommon.Ty.F64 (TermIR.MkMem (TermIR.Mem.AtPtr p) Nothing 8))
                [t] <- strings Types.StringRoutine.ShowDouble [f]
                pure (set env r t)
              -- a string as the double it reads as
              else if from == StringType && to == DoubleType then do
                [f] <- strings Types.StringRoutine.ReadDouble [get env x]
                p <- TermIR.Build.emit1 (TermIR.Instr.AllocObj Types.Header.DoubleH [f])
                d <- TermIR.Build.emit1 (TermIR.Instr.WidenPtr p)
                pure (set env r d)
              else TermIR.Build.unsupported ("the cast from " ++ show from ++ " to " ++ show to)
            _ => TermIR.Build.unsupported ("the cast from " ++ show from ++ " to " ++ show to)
          (BelieveMe, [_, _, x]) => pure (set env r (get env x))
          (fn, args) => set env r <$> value fn args
          where
            ||| A cast to `Char`: the value if it is a Unicode scalar value, 0 if not.
            toChar : IntWidth -> TermIR.Opnd v IRCommon.Ty.Val -> B (TermIR.Opnd v IRCommon.Ty.Val)
            toChar wf x = do
              w <- case wf of
                Narrow _ _ => fixValue x
                Wide _ => wideWord x
                Unbounded => do
                  [w] <- TermIR.Build.joinPoint [IRCommon.Ty.W64] $ \done =>
                    TermIR.Build.ifFixnums [x] (\[f] => do w <- untag (f); done [w]) (done [TermIR.Opnd.W (-1)])
                  pure w
              [r] <- TermIR.Build.joinPoint [IRCommon.Ty.Val] $ \done => do
                keep <- TermIR.Build.block [] $ \[] => do f <- TermIR.Build.emit1 (TermIR.Instr.Tag w)
                                                          r <- widen f
                                                          done [r]
                zero <- TermIR.Build.block [] $ \[] => done [TermIR.Opnd.Vx {enc} 0]
                TermIR.Build.branch IRCommon.Op.LtS w (TermIR.Opnd.W 0) (zero []) $
                  TermIR.Build.branch IRCommon.Op.LeS w (TermIR.Opnd.W 55295) (keep []) $
                    TermIR.Build.branch IRCommon.Op.LtS w (TermIR.Opnd.W 57344) (zero []) $
                      TermIR.Build.branch IRCommon.Op.LeS w (TermIR.Opnd.W 1114111) (keep []) (zero [])
              pure r

            ||| A word wrapped to a narrow width, as a uniform value: a fixnum, which it
            ||| always fits.
            narrowVal : Nat -> Bool -> TermIR.Opnd v IRCommon.Ty.W64 -> B (TermIR.Opnd v IRCommon.Ty.Val)
            narrowVal n s w = do
              e <- TermIR.Build.emit1 (TermIR.Instr.Ext (subWord n) s w)
              f <- TermIR.Build.emit1 (TermIR.Instr.Tag e)
              widen f
              where
                subWord : Nat -> IRCommon.Op.SubWord
                subWord 8 = IRCommon.Op.Sub8
                subWord 16 = IRCommon.Op.Sub16
                subWord _ = IRCommon.Op.Sub32

            ||| A uniform integer of one width as one of another, wrapping as Idris's
            ||| casts do.
            retype : IntWidth -> IntWidth -> TermIR.Opnd v IRCommon.Ty.Val -> B (TermIR.Opnd v IRCommon.Ty.Val)
            retype wf wt x =
              if keeps wf wt then pure x else case (wf, wt) of
                (Narrow _ _, Narrow n s) => fixValue x >>= narrowVal n s
                (Wide _, Narrow n s) => wideWord x >>= narrowVal n s
                (Unbounded, Narrow n s) => integerBits x >>= narrowVal n s
                (Unbounded, Wide _) => do
                  [r] <- TermIR.Build.joinPoint [IRCommon.Ty.Val] $ \done =>
                    TermIR.Build.ifFixnums [x] (\_ => done [x]) (do a <- integerBits x; r <- wideVal a; done [r])
                  pure r
                (Wide True, Unbounded) => do
                  [r] <- TermIR.Build.joinPoint [IRCommon.Ty.Val] $ \done =>
                    TermIR.Build.ifFixnums [x] (\_ => done [x])
                      (do a <- boxWord x
                          [r] <- integers Types.IntegerRoutine.FromInt64 [a]
                          done [r])
                  pure r
                (Wide False, Unbounded) => do
                  a <- wideWord x
                  [r] <- TermIR.Build.joinPoint [IRCommon.Ty.Val] $ \done =>
                    TermIR.Build.branch IRCommon.Op.LtU a (TermIR.Opnd.W 4611686018427387904)
                      (do f <- TermIR.Build.emit1 (TermIR.Instr.Tag a); r <- widen f; done [r])
                      (do [r] <- integers Types.IntegerRoutine.FromBits64 [a]
                          done [r])
                  pure r
                _ => pure x
              where
                ||| Whether every value of the first width is a value of the second, held the
                ||| same way, so that a cast between them is a move.
                keeps : IntWidth -> IntWidth -> Bool
                keeps (Wide _) (Wide _) = True
                keeps (Narrow _ _) (Wide _) = True
                keeps (Narrow _ _) Unbounded = True
                keeps Unbounded Unbounded = True
                keeps (Narrow n s) (Narrow m t) = if s == t then m >= n else not s && t && m > n
                keeps _ _ = False

                ||| An `Integer`'s value modulo 2^64, as a word.
                integerBits : TermIR.Opnd v IRCommon.Ty.Val -> B (TermIR.Opnd v IRCommon.Ty.W64)
                integerBits x = do
                  [w] <- TermIR.Build.joinPoint [IRCommon.Ty.W64] $ \done =>
                    TermIR.Build.ifFixnums [x] (\[f] => do w <- untag (f); done [w])
                      (do [w] <- integers Types.IntegerRoutine.ToBits64 [x]
                          done [w])
                  pure w

            ||| A word known to be in the fixnum range, as a value: a count or a code
            ||| point.
            wordFix : TermIR.Opnd v IRCommon.Ty.W64 -> B (TermIR.Opnd v IRCommon.Ty.Val)
            wordFix w = do f <- TermIR.Build.emit1 (TermIR.Instr.Tag w); TermIR.Build.emit1 (TermIR.Instr.WidenFix f)

            ||| A word in decimal, signed or not, by the string routine for it.
            decimalWord : Bool -> TermIR.Opnd v IRCommon.Ty.W64 -> B (TermIR.Opnd v IRCommon.Ty.Val)
            decimalWord True w = do [t] <- strings Types.StringRoutine.ShowSigned [w]; pure t
            decimalWord False w = do [t] <- strings Types.StringRoutine.ShowUnsigned [w]; pure t

            ||| A number of the width in decimal, by its word; an `Integer` outside
            ||| the fixnums is not yet.
            decimal : IntWidth -> TermIR.Opnd v IRCommon.Ty.Val -> B (TermIR.Opnd v IRCommon.Ty.Val)
            decimal (Narrow _ signed) x = do w <- fixValue x; decimalWord signed w
            decimal (Wide signed) x = do w <- wideWord x; decimalWord signed w
            decimal Unbounded x = do
              [t] <- TermIR.Build.joinPoint [IRCommon.Ty.Val] $ \done =>
                TermIR.Build.ifFixnums [x] (\[f] => do w <- untag f
                                                       t <- decimalWord True w
                                                       done [t])
                  (TermIR.Build.unsupported "an Integer outside the fixnum range as text")
              pure t

            ||| A comparison of strings: the runtime's order, -1, 0 or 1, against 0.
            stringOrder : IRCommon.Op.Rel -> TermIR.Opnd v IRCommon.Ty.Val -> TermIR.Opnd v IRCommon.Ty.Val ->
                          B (TermIR.Opnd v IRCommon.Ty.Val)
            stringOrder rel x y = do
              [o] <- strings Types.StringRoutine.Compare [x, y]
              b <- TermIR.Build.emit1 (TermIR.Instr.Cmp rel o (TermIR.Opnd.W 0))
              wordFix b

            ||| A call of an `Integer` routine on values that gives one, chosen as the
            ||| program is compiled: its operands and its result as its port's
            ||| registers.
            integerCall : Types.IntegerRoutine -> List (TermIR.Opnd v IRCommon.Ty.Val) -> B (TermIR.Opnd v IRCommon.Ty.Val)
            integerCall c xs = case (Linkage.Routine.integerRoutine refs.realised c, operands (Linkage.Routine.portParams (Types.IntegerRoutine.port c)) xs) of
              (Nothing, _) => TermIR.Build.unsupported "an Integer operation beyond the fixnums, which the runtime has none of yet"
              (Just name, Just os) => do
                rs <- callRoutine name {rs = Linkage.Routine.portResults (Types.IntegerRoutine.port c)} os
                maybe (TermIR.Build.crash ("the Integer routine " ++ show name ++ " gives no value")) pure (one rs)
              (Just name, Nothing) => TermIR.Build.crash ("the Integer routine " ++ show name ++ " takes other operands")
              where

                operands : (ts : List (IRCommon.Ty enc)) -> List (TermIR.Opnd v IRCommon.Ty.Val) ->
                           Maybe (All (TermIR.Opnd v) ts)
                operands [] [] = Just []
                operands (IRCommon.Ty.Val :: ts) (x :: more) = (x ::) <$> operands ts more
                operands _ _ = Nothing

                one : {ts : List (IRCommon.Ty enc)} -> All (TermIR.Opnd v) ts -> Maybe (TermIR.Opnd v IRCommon.Ty.Val)
                one {ts = [IRCommon.Ty.Val]} [r] = Just r
                one _ = Nothing

            negation : IntWidth -> TermIR.Opnd v IRCommon.Ty.Val -> B (TermIR.Opnd v IRCommon.Ty.Val)
            negation (Narrow n s) x = do
              a <- fixValue x
              w <- TermIR.Build.emit1 (TermIR.Instr.Unary IRCommon.Op.Negate a)
              narrowVal n s w
            negation (Wide _) x = do
              [r] <- TermIR.Build.joinPoint [IRCommon.Ty.Val] $ \done => do
                word <- TermIR.Build.block [IRCommon.Ty.W64] $ \[wa] => do
                  w <- TermIR.Build.emit1 (TermIR.Instr.Unary IRCommon.Op.Negate wa)
                  r <- wideVal w
                  done [r]
                TermIR.Build.ifFixnums [x]
                  (\[a] => TermIR.Build.arithOv TermIR.OvOp.OvSub (TermIR.Opnd.Fx 0) a (\f => do r <- widen f; done [r])
                             (do wa <- untag (a); word [wa]))
                  (do wa <- wideWord x; word [wa])
              pure r
            negation Unbounded x = do
              [r] <- TermIR.Build.joinPoint [IRCommon.Ty.Val] $ \done => do
                slow <- TermIR.Build.block [] $ \[] => do r <- integerCall Types.IntegerRoutine.Neg [x]; done [r]
                TermIR.Build.ifFixnums [x]
                  (\[a] =>
                    TermIR.Build.arithOv TermIR.OvOp.OvSub (TermIR.Opnd.Fx 0) a (\f => do r <- widen f; done [r])
                   (slow []))
                    (slow [])
              pure r

            ||| `div` or `mod`.
            division : IntWidth -> (remainder : Bool) -> (x, y : TermIR.Opnd v IRCommon.Ty.Val) ->
                       B (TermIR.Opnd v IRCommon.Ty.Val)
            division (Narrow n s) m x y = do
              a <- fixValue x
              b <- fixValue y
              Words.nonZero b
              w <- Words.divide s m a b
              narrowVal n s w
            division (Wide s) m x y = do
              a <- wideWord x
              b <- wideWord y
              Words.nonZero b
              w <- Words.divide s m a b
              wideVal w
            division Unbounded m x y = do
              [r] <- TermIR.Build.joinPoint [IRCommon.Ty.Val] $ \done => do
                slow <- TermIR.Build.block [] $ \[] => do r <- integerCall (if m then Types.IntegerRoutine.Mod else Types.IntegerRoutine.Div) [x, y]; done [r]
                TermIR.Build.ifFixnums [x, y]
                  (\[fa, fb] => do
                     a <- untag (fa)
                     b <- untag (fb)
                     TermIR.Build.branch IRCommon.Op.EqR b (TermIR.Opnd.W 0) (slow []) $ do
                       w <- Words.divide True m a b
                       TermIR.Build.tagOv w (\f => do r <- widen f; done [r]) (slow []))
                  (slow [])
              pure r

            ||| `shiftL` or `shiftR`: arithmetic on signed types, logical on unsigned.
            shifting : IntWidth -> (left : Bool) -> (x, y : TermIR.Opnd v IRCommon.Ty.Val) ->
                       B (TermIR.Opnd v IRCommon.Ty.Val)
            shifting (Narrow n s) left x y = do
              a <- fixValue x
              k <- fixValue y
              w <- Words.shiftBy (if left then IRCommon.Op.Shl else if s then IRCommon.Op.Sar else IRCommon.Op.Shr) a k
              narrowVal n s w
            shifting (Wide s) left x y = do
              a <- wideWord x
              k <- wideWord y
              w <- Words.shiftBy (if left then IRCommon.Op.Shl else if s then IRCommon.Op.Sar else IRCommon.Op.Shr) a k
              wideVal w
            shifting Unbounded left x y = do
              [r] <- TermIR.Build.joinPoint [IRCommon.Ty.Val] $ \done => do
                slow <- TermIR.Build.block [] $ \[] => do r <- integerCall (if left then Types.IntegerRoutine.Shl else Types.IntegerRoutine.Shr) [x, y]
                                                          done [r]
                TermIR.Build.ifFixnums [x, y]
                  (\[fa, fk] => do
                     a <- untag (fa)
                     k <- untag (fk)
                     TermIR.Build.branch IRCommon.Op.LtS k (TermIR.Opnd.W 0) (slow []) $
                       if left
                          then -- shift by at most 62, and keep the result only if
                               -- shifting back gives the operand and it is a fixnum
                               TermIR.Build.branch IRCommon.Op.GtS k (TermIR.Opnd.W 62) (slow []) $ do
                                 w <- TermIR.Build.emit1 (TermIR.Instr.Arith IRCommon.Op.Shl a k)
                                 back <- TermIR.Build.emit1 (TermIR.Instr.Arith IRCommon.Op.Sar w k)
                                 TermIR.Build.branch IRCommon.Op.NeR back a (slow []) $
                                   TermIR.Build.tagOv w (\f => do r <- widen f; done [r]) (slow [])
                          else do
                            w <- Words.shiftBy IRCommon.Op.Sar a k
                            f <- TermIR.Build.emit1 (TermIR.Instr.Tag w)
                            r <- widen f
                            done [r])
                  (slow [])
              pure r

            withWidth : PrimType -> String -> (IntWidth -> B a) -> B a
            withWidth ty what k = case intWidth ty of
              Just w => k w
              Nothing => TermIR.Build.unsupported (what ++ " on " ++ show ty)

            ||| Addition, subtraction, multiplication and the bitwise operations, with
            ||| the operation's `Integer` routine.
            arithmetic : IntWidth -> IRCommon.Op.ArithOp -> (routine : Types.IntegerRoutine) ->
                         (x, y : TermIR.Opnd v IRCommon.Ty.Val) -> B (TermIR.Opnd v IRCommon.Ty.Val)
            arithmetic width o routine x y = case width of
              Narrow n s => do
                a <- fixValue x
                b <- fixValue y
                w <- TermIR.Build.emit1 (TermIR.Instr.Arith o a b)
                narrowVal n s w
              Wide _ => do
                [r] <- TermIR.Build.joinPoint [IRCommon.Ty.Val] $ \done => do
                  words <- TermIR.Build.block [IRCommon.Ty.W64, IRCommon.Ty.W64] $ \[wa, wb] => do
                    w <- TermIR.Build.emit1 (TermIR.Instr.Arith o wa wb)
                    r <- wideVal w
                    done [r]
                  TermIR.Build.ifFixnums [x, y]
                    (\[a, b] => case ovOp o of
                       Just ov => TermIR.Build.arithOv ov a b (\f => do r <- widen f; done [r])
                                    (do wa <- untag (a); wb <- untag (b); words [wa, wb])
                       Nothing => do f <- TermIR.Build.emit1 (TermIR.Instr.Arith o a b); r <- widen f; done [r])
                    (do wa <- wideWord x; wb <- wideWord y; words [wa, wb])
                pure r
              Unbounded => do
                [r] <- TermIR.Build.joinPoint [IRCommon.Ty.Val] $ \done => do
                  slow <- TermIR.Build.block [] $ \[] => do r <- integerCall routine [x, y]; done [r]
                  TermIR.Build.ifFixnums [x, y]
                    (\[a, b] => case ovOp o of
                       Just ov => TermIR.Build.arithOv ov a b (\f => do r <- widen f; done [r]) (slow [])
                       Nothing => do f <- TermIR.Build.emit1 (TermIR.Instr.Arith o a b); r <- widen f; done [r])
                    (slow [])
                pure r
              where
                ||| The overflow form of an operation that has one.
                ovOp : IRCommon.Op.ArithOp -> Maybe TermIR.OvOp
                ovOp Add = Just TermIR.OvOp.OvAdd
                ovOp Sub = Just TermIR.OvOp.OvSub
                ovOp Mul = Just TermIR.OvOp.OvMul
                ovOp _ = Nothing

            ||| A comparison, giving the `Int` 0 or 1.
            comparison : IntWidth -> IRCommon.Op.Rel -> (x, y : TermIR.Opnd v IRCommon.Ty.Val) ->
                         B (TermIR.Opnd v IRCommon.Ty.Val)
            comparison width rel x y = case width of
              Narrow _ _ => do
                a <- asFix x
                b <- asFix y
                c <- TermIR.Build.emit1 (TermIR.Instr.Cmp rel a b)
                boolVal c
              Wide s => do
                let rel' = if s then rel else unsignedRel rel
                [c] <- TermIR.Build.joinPoint [IRCommon.Ty.W64] $ \done =>
                  TermIR.Build.ifFixnums [x, y]
                    (\[a, b] => do c <- TermIR.Build.emit1 (TermIR.Instr.Cmp rel' a b); done [c])
                    (do a <- wideWord x; b <- wideWord y; c <- TermIR.Build.emit1 (TermIR.Instr.Cmp rel' a b); done [c])
                boolVal c
              Unbounded => do
                [c] <- TermIR.Build.joinPoint [IRCommon.Ty.W64] $ \done =>
                  TermIR.Build.ifFixnums [x, y]
                    (\[a, b] => do c <- TermIR.Build.emit1 (TermIR.Instr.Cmp rel a b); done [c])
                    (do [o] <- integers Types.IntegerRoutine.Compare [x, y]
                        c <- TermIR.Build.emit1 (TermIR.Instr.Cmp rel o (TermIR.Opnd.W 0))
                        done [c])
                boolVal c
              where
                ||| The unsigned relation for a signed one.
                unsignedRel : IRCommon.Op.Rel -> IRCommon.Op.Rel
                unsignedRel IRCommon.Op.LtS = IRCommon.Op.LtU
                unsignedRel IRCommon.Op.LeS = IRCommon.Op.LeU
                unsignedRel IRCommon.Op.GtS = IRCommon.Op.GtU
                unsignedRel IRCommon.Op.GeS = IRCommon.Op.GeU
                unsignedRel r = r

                ||| A comparison's 0 or 1, as the `Int` Idris's comparisons give.
                boolVal : TermIR.Opnd v IRCommon.Ty.W64 -> B (TermIR.Opnd v IRCommon.Ty.Val)
                boolVal c = TermIR.Build.emit1 (TermIR.Instr.Tag c) >>= widen

            value : PrimFn m -> Vect m Reg -> B (TermIR.Opnd v IRCommon.Ty.Val)
            value (Add ty) [x, y] = withWidth ty "addition" (\w => arithmetic w Add Types.IntegerRoutine.Add (get env x) (get env y))
            value (Sub ty) [x, y] = withWidth ty "subtraction" (\w => arithmetic w Sub Types.IntegerRoutine.Sub (get env x) (get env y))
            value (Mul ty) [x, y] = withWidth ty "multiplication" (\w => arithmetic w Mul Types.IntegerRoutine.Mul (get env x) (get env y))
            value (Div ty) [x, y] = withWidth ty "division" (\w => division w False (get env x) (get env y))
            value (Mod ty) [x, y] = withWidth ty "remainder" (\w => division w True (get env x) (get env y))
            value (Neg ty) [x] = withWidth ty "negation" (\w => negation w (get env x))
            value (ShiftL ty) [x, y] = withWidth ty "a left shift" (\w => shifting w True (get env x) (get env y))
            value (ShiftR ty) [x, y] = withWidth ty "a right shift" (\w => shifting w False (get env x) (get env y))
            value (BAnd ty) [x, y] =
              withWidth ty "bitwise and" (\w => arithmetic w IRCommon.Op.And Types.IntegerRoutine.And (get env x) (get env y))
            value (BOr ty) [x, y] =
              withWidth ty "bitwise or" (\w => arithmetic w IRCommon.Op.Or Types.IntegerRoutine.Or (get env x) (get env y))
            value (BXOr ty) [x, y] =
              withWidth ty "bitwise xor" (\w => arithmetic w IRCommon.Op.Xor Types.IntegerRoutine.Xor (get env x) (get env y))
            -- the string primitives: the runtime's routines under the encoding
            value StrLength [s] = do [n] <- strings Types.StringRoutine.Length [get env s]
                                     wordFix n
            value StrHead [s] = do [c] <- strings Types.StringRoutine.Head [get env s]
                                   wordFix c
            value StrTail [s] = do [r] <- strings Types.StringRoutine.Tail [get env s]
                                   pure r
            value StrIndex [s, i] = do
              w <- wideWord (get env i)
              [c] <- strings Types.StringRoutine.Index [get env s, w]
              wordFix c
            value StrCons [c, s] = do
              w <- fixValue (get env c)
              [r] <- strings Types.StringRoutine.Cons [w, get env s]
              pure r
            value StrAppend [a, b] = do [r] <- strings Types.StringRoutine.Append [get env a, get env b]
                                        pure r
            value StrReverse [s] = do [r] <- strings Types.StringRoutine.Reverse [get env s]
                                      pure r
            value StrSubstr [o, l, s] = do
              wo <- wideWord (get env o)
              wl <- wideWord (get env l)
              [r] <- strings Types.StringRoutine.Substr [wo, wl, get env s]
              pure r
            value (LT StringType) [x, y] = stringOrder IRCommon.Op.LtS (get env x) (get env y)
            value (LTE StringType) [x, y] = stringOrder IRCommon.Op.LeS (get env x) (get env y)
            value (EQ StringType) [x, y] = stringOrder IRCommon.Op.EqR (get env x) (get env y)
            value (GTE StringType) [x, y] = stringOrder IRCommon.Op.GeS (get env x) (get env y)
            value (GT StringType) [x, y] = stringOrder IRCommon.Op.GtS (get env x) (get env y)
            value (LT ty) [x, y] = withWidth ty "<" (\w => comparison w IRCommon.Op.LtS (get env x) (get env y))
            value (LTE ty) [x, y] = withWidth ty "<=" (\w => comparison w IRCommon.Op.LeS (get env x) (get env y))
            value (EQ ty) [x, y] = withWidth ty "==" (\w => comparison w IRCommon.Op.EqR (get env x) (get env y))
            value (GTE ty) [x, y] = withWidth ty ">=" (\w => comparison w IRCommon.Op.GeS (get env x) (get env y))
            value (GT ty) [x, y] = withWidth ty ">" (\w => comparison w IRCommon.Op.GtS (get env x) (get env y))
            value fn _ = TermIR.Build.unsupported ("the primitive " ++ show fn)

------------------------------------------------------------------------------
-- The program

||| What a function of the program is lowered from.
data Plan
  = ||| A VMCode function.
    FromVM (List Int) (List VMInst)
  | ||| A function that has a flat form, of the arity: a wrapper around the
    ||| form's `Direct` function, with the shapes of its parameters and of its
    ||| result.
    Boundary Nat Flat.Exp.FlatDef (List Flat.Exp.Shape) Flat.Exp.Shape
  | ||| A flat form: its `Direct` function.
    Form Flat.Exp.FlatDef
  | ||| A foreign function, of the arity.
    Foreign Nat
  | ||| The entry, when the program has none.
    NoEntry

parameters {enc : Types.Enc} {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val}

  ||| A function that has a flat form, as the wrapper around the form's.
  lowerBoundary : (d : TermIR.Decls enc) -> Refs enc d -> LowerFlat.Callee d -> List Flat.Exp.Shape -> Flat.Exp.Shape ->
                  (arity : Nat) ->
                  TermIR.Build.Closed d IRCommon.Conv.CPS False (replicate arity IRCommon.Ty.Val)
  lowerBoundary d refs ce ss r arity = TermIR.Build.build $ \ps => boundary d refs ce ss r (allVals ps)

  ||| A function's definition, from its plan.
  defOf : (d : TermIR.Decls enc) -> Refs enc d -> LowerFlat.Forms enc d -> (s : TermIR.Sig enc) -> Plan ->
          TermIR.Def d s
  defOf d refs fs (TermIR.MkSig n IRCommon.Conv.CPS ps False) (FromVM args body) =
    case decEq ps (replicate (length args) IRCommon.Ty.Val) of
    Yes Refl =>
      TermIR.Def.Defined
        (fromMaybe (TermIR.Body.Unsupported "a level outside its context")
         (TermIR.Build.close (lowerFunction d refs args body)))
    No _ => TermIR.Def.Defined (TermIR.Body.Unsupported ("the parameters of " ++ show n))
    where
      ||| A VMCode function: its parameters are its locals at entry, and it
      ||| returns its result register.
      lowerFunction : (d : TermIR.Decls enc) -> Refs enc d -> (args : List Int) -> List VMInst ->
                      TermIR.Build.Closed d IRCommon.Conv.CPS False (replicate (length args) IRCommon.Ty.Val)
      lowerFunction d refs args body = TermIR.Build.build $ \ps =>
        lower d refs (fromList (zip args (map (\x => (x, Nothing)) (allVals ps)))) True (annotate (singleton (-1)) body)
              (\env => TermIR.Build.return (get env RVal))
  defOf d refs fs (TermIR.MkSig n IRCommon.Conv.CPS ps False) (Boundary arity fd ss r) =
    case (decEq ps (replicate arity IRCommon.Ty.Val), lookup fd.name fs.callees) of
      (Yes Refl, Just ce) =>
        TermIR.Def.Defined
          (fromMaybe (TermIR.Body.Unsupported "a level outside its context")
           (TermIR.Build.close (lowerBoundary d refs ce ss r arity)))
      _ => TermIR.Def.Defined (TermIR.Body.Unsupported ("the boundary of " ++ show n))
  defOf d refs fs (TermIR.MkSig n (IRCommon.Conv.Direct rs False) ps cv) (Form fd) =
    case (decEq rs (LowerFlat.tys fd.result),
      decEq ps (LowerFlat.tys (LowerFlat.paramsLayout fd.params)), decEq cv (Linkage.ConvertsIn.convertsIn fd.name)) of
      (Yes Refl, Yes Refl, Yes Refl) =>
        TermIR.Def.Defined
          (fromMaybe (TermIR.Body.Unsupported "a level outside its context")
           (TermIR.Build.close (LowerFlat.lowerForm d fs fd)))
      _ => TermIR.Def.Defined (TermIR.Body.Unsupported ("the registers of the flat form of " ++ show fd.name))
  defOf d refs fs (TermIR.MkSig n IRCommon.Conv.CPS ps False) (Foreign arity) =
    case decEq ps (replicate arity IRCommon.Ty.Val) of
    Yes Refl =>
      TermIR.Def.Defined
        (fromMaybe (TermIR.Body.Unsupported "a level outside its context")
         (TermIR.Build.close (lowerForeign d refs n arity)))
    No _ => TermIR.Def.Defined (TermIR.Body.Unsupported ("the parameters of " ++ show n))
    where
      ||| A foreign function the runtime does not implement: the abort stub.
      lowerForeign : (d : TermIR.Decls enc) -> Refs enc d -> Name -> (arity : Nat) ->
                     TermIR.Build.Closed d IRCommon.Conv.CPS False (replicate arity IRCommon.Ty.Val)
      lowerForeign d refs n arity = TermIR.Build.build $ \ps =>
        TermIR.Build.unsupported ("the foreign function " ++ show n)
  defOf d refs fs s NoEntry = TermIR.Def.Defined (TermIR.Body.Unsupported "a program without __mainExpression")
  defOf d refs fs s _ = TermIR.Def.Defined (TermIR.Body.Unsupported ("the definition of " ++ show s.name))

  defs : (d : TermIR.Decls enc) -> Refs enc d -> LowerFlat.Forms enc d -> (es : List (TermIR.Sig enc, Plan)) ->
         All (TermIR.Def d) (map Builtin.fst es)
  defs d refs fs [] = []
  defs d refs fs ((s, p) :: es) = defOf d refs fs s p :: defs d refs fs es

||| The program of the declarations, the entry first.
program : {enc : Types.Enc} -> {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} -> List Flat.Exp.FlatDef ->
          Flat.Exp.Shapes -> Linkage.Realised -> (tables : SortedMap Name (Int, Nat)) -> Plan ->
          (es : List (TermIR.Sig enc, Plan)) -> (rs : List (s ** ({0 d : TermIR.Decls enc} -> TermIR.StaticDef d s))) ->
            TermIR.Program.TermProgram enc
program forms shapes realised tables entry es rs =
  case choose
    (Data.Distinct.distinct (map (.name) (mainSig :: map Builtin.fst es))
     && Data.Distinct.distinct (map (.sym) (map DPair.fst rs))) of
    Left ok =>
      (declsOf es rs ** TermIR.MkProgram
                     (defs (declsOf es rs) (refsOf (declsOf es rs))
                       (LowerFlat.MkForms (LowerFlat.callees (declsOf es rs) forms) shapes realised.services
                         realised.externs realised.primitives tables)
                           ((mainSig, entry) :: es))
                     (staticDefs (declsOf es rs) rs) (TermIR.Program.MkEntry TermIR.Var.here) IRCommon.ConIds.noConIds)
    Right _ =>
      (TermIR.MkDecls [mainSig] [] ** TermIR.MkProgram
                     [TermIR.Def.Defined (TermIR.Body.Unsupported "a program with two definitions of one name")] []
                       (TermIR.Program.MkEntry TermIR.Var.here) IRCommon.ConIds.noConIds)
  where
    refsOf : (d : TermIR.Decls enc) -> Refs enc d
    refsOf d = MkRefs (fromList [(s.name, (s ** v)) | (s ** v) <- TermIR.Var.enumerate d.sigs])
                      (fromList [(s.sym, (s ** v)) | (s ** v) <- TermIR.Var.enumerate d.statics]) realised

    staticDefs : (d : TermIR.Decls enc) -> (rs : List (s ** ({0 d' : TermIR.Decls enc} -> TermIR.StaticDef d' s))) ->
                 All (TermIR.StaticDef d) (map DPair.fst rs)
    staticDefs d [] = []
    staticDefs d ((_ ** def) :: rs) = def :: staticDefs d rs

    ||| The entry's signature: CPS, of no parameters.
    mainSig : TermIR.Sig enc'
    mainSig = TermIR.MkSig mainExpression IRCommon.Conv.CPS [] False

    ||| The declarations: the entry first, the other functions, the statics.
    declsOf : (es : List (TermIR.Sig enc, Plan)) ->
              (rs : List (s ** ({0 d : TermIR.Decls enc} -> TermIR.StaticDef d s))) -> TermIR.Decls enc
    declsOf es rs = TermIR.MkDecls (mainSig :: map Builtin.fst es) (map DPair.fst rs)

||| Whether a value of the C type is held as a flat value of the skeleton:
||| an integer as its machine type, a `Char`, a `Double`, the world, `()`, a
||| primitive's `IORes`, a `String` held as ordinary code holds it, and a
||| pointer, `Ptr a` or `AnyPtr`, held as ordinary code holds it, an object
||| of its address.
export
cfAgrees : CFType -> Flat.Exp.Skeleton -> Bool
cfAgrees CFInt (Flat.Exp.SPrim IntType) = True
cfAgrees CFInt8 (Flat.Exp.SPrim Int8Type) = True
cfAgrees CFInt16 (Flat.Exp.SPrim Int16Type) = True
cfAgrees CFInt32 (Flat.Exp.SPrim Int32Type) = True
cfAgrees CFInt64 (Flat.Exp.SPrim Int64Type) = True
cfAgrees CFUnsigned8 (Flat.Exp.SPrim Bits8Type) = True
cfAgrees CFUnsigned16 (Flat.Exp.SPrim Bits16Type) = True
cfAgrees CFUnsigned32 (Flat.Exp.SPrim Bits32Type) = True
cfAgrees CFUnsigned64 (Flat.Exp.SPrim Bits64Type) = True
cfAgrees CFChar (Flat.Exp.SPrim CharType) = True
cfAgrees CFDouble (Flat.Exp.SPrim DoubleType) = True
cfAgrees CFWorld (Flat.Exp.SPrim WorldType) = True
cfAgrees CFUnit (Flat.Exp.SCon n []) = n == NS (mkNamespace "Builtin") (UN (Basic "Unit"))
cfAgrees (CFIORes t) (Flat.Exp.SCon n [s]) = n == NS (mkNamespace "PrimIO") (UN (Basic "IORes")) && cfAgrees t s
cfAgrees CFString (Flat.Exp.SCon n [Flat.Exp.SPrim StringType]) = n == Flat.Exp.uniformType
cfAgrees CFPtr (Flat.Exp.SCon n [Flat.Exp.SCon p _]) =
  n == Flat.Exp.uniformType
  && (p == NS (mkNamespace "PrimIO") (UN (Basic "Ptr")) || p == NS (mkNamespace "PrimIO") (UN (Basic "AnyPtr")))
cfAgrees (CFUser t _) (Flat.Exp.SCon n [Flat.Exp.SCon t' _]) = n == Flat.Exp.uniformType && t == t'
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
||| A foreign function the runtime implements (`Native.Codegen.Linkage.
||| foreignFunctions`) becomes the boundary to the runtime's function, which
||| must take and return, position by position, what the foreign function's
||| C types say; one that does not is an error.
|||
||| The runtime's routines, as the loaded runtime realises the contract
||| (`Native.Codegen.Linkage.Realised`), are forms among them: a routine the
||| runtime has must have a form, of its port's registers, or the program
||| is not lowered, and the error says which. A call of one it does not have
||| yet, of an encoding it has no module for, ends the program as
||| `Unsupported` does. The OS services' externs lower to calls
||| of the platform's functions for them, and the inline externs to the
||| instructions they stand for.
export
lowerProgram : (enc : Types.Enc) -> {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} -> Platform ->
               Linkage.Realised -> List Flat.Exp.FlatDef -> Flat.Exp.Shapes -> (tables : SortedMap Name (Int, Nat)) ->
               List (Name, VMDef) -> Either String (TermIR.Program.TermProgram enc)
lowerProgram enc platform realised forms shapes tables vmdefs = do
  traverse_ provided (Linkage.Routine.routines {enc} realised)
  traverse_ agrees (mapMaybe boundForeign vmdefs)
  let entryPlan = case Data.List.lookup mainExpression vmdefs of
                    Just (MkVMFun [] body) => FromVM [] body
                    _ => NoEntry
      planned = mapMaybe plan (filter ((/= mainExpression) . fst) vmdefs)
      others = planned
                 ++ [(LowerFlat.formSig fd, Form fd) | fd <- forms]
      boxing = fromList [(nullaryCon c, Nullary c) | c <- toList (concatMap (boxed . snd) planned)]
      statics = Data.SortedMap.toList (foldl mergeLeft boxing (mapMaybe bodyStatics vmdefs))
  pure
    (program forms shapes realised tables entryPlan others (mapMaybe ready statics))
  where
    -- A routine the runtime has: its form, of its port's registers.
    provided : Linkage.Routine.RoutineCall enc -> Either String ()
    provided r =
      case find (\fd => fd.name == r.name) forms of
        Nothing => Left ("the runtime has no routine " ++ show r.name ++ ", which generated code calls")
        Just fd =>
          let rs = LowerFlat.tys {enc} fd.result
              ps = LowerFlat.tys {enc} (LowerFlat.paramsLayout fd.params)
          in if rs == r.results && ps == r.params then Right ()
             else Left ("the runtime's " ++ show r.name ++ " has the form "
                        ++ show ps ++ " -> " ++ show rs
                        ++ ", but its port is "
                        ++ show r.params ++ " -> " ++ show r.results)

    byName : SortedMap Name Flat.Exp.FlatDef
    byName = fromList [(fd.name, fd) | fd <- forms]

    boundForeign : (Name, VMDef) -> Maybe (Name, List CFType, CFType)
    boundForeign (n, MkVMForeign _ fargs ret) = if elem n (map fst (Linkage.ForeignFunctions.foreignFunctions enc))
      then Just (n, fargs, ret) else Nothing
    boundForeign _ = Nothing

    -- A foreign function and its implementation, position by position.
    agrees : (Name, List CFType, CFType) -> Either String ()
    agrees (n, fargs, ret) = case Data.List.lookup n (Linkage.ForeignFunctions.foreignFunctions enc) >>= \f =>
      lookup f byName of
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
      fd <- lookup n byName
        <|> (Data.List.lookup n (Linkage.ForeignFunctions.foreignFunctions enc) >>= \f => lookup f byName)
      guard (length fd.params == arity)
      ss <- traverse (Flat.Exp.shapeOf shapes . skeleton) fd.params
      r <- Flat.Exp.shapeOf shapes fd.resultSkeleton
      guard (map Flat.Exp.shapeLayout ss == map layout fd.params && Flat.Exp.shapeLayout r == fd.result)
      pure (Boundary arity fd ss r)

    ||| The ids of the constructors of no fields that ordinary code represents
    ||| as objects, in a shape: the statics boxing a value of it may need.
    nullaries : Flat.Exp.Shape -> Data.Builder Int
    nullaries (Flat.Exp.PrimShape _) = neutral
    nullaries Flat.Exp.UniformShape = neutral
    nullaries (Flat.Exp.DataShape cs) = concatMap con cs
      where
        con : Flat.Exp.ConShape -> Data.Builder Int
        con c = (case (c.ordinary, c.fields) of
                   (Flat.Exp.AsObject cid, []) => Data.Builder.single cid
                   _ => neutral) <+> concatMap nullaries c.fields

    -- The nullary constructors a boundary may box.
    boxed : Plan -> Data.Builder Int
    boxed (Boundary _ _ ss r) = concatMap nullaries (r :: ss)
    boxed _ = neutral

    plan : (Name, VMDef) -> Maybe (TermIR.Sig enc, Plan)
    plan (n, MkVMFun args body) =
      Just (TermIR.MkSig n IRCommon.Conv.CPS (replicate (length args) IRCommon.Ty.Val) False,
            fromMaybe (FromVM args body) (boundaryOf n (length args)))
    plan (n, MkVMForeign _ fargs _) =
      Just (TermIR.MkSig n IRCommon.Conv.CPS (replicate (length fargs) IRCommon.Ty.Val) False,
            fromMaybe (Foreign (length fargs)) (boundaryOf n (length fargs)))
    plan (n, MkVMError _) = Nothing

    ||| The constants a function's locals may hold, and the static objects its
    ||| constants need. A cast of a local holding a constant is folded while
    ||| compiling, so every constant a local may hold is followed through casts;
    ||| the result may name statics the lowering does not use, which costs only
    ||| their bytes.
    staticsOf : List VMInst -> SortedMap Name StaticPlan
    staticsOf body = snd (go body (empty, note (Str "") empty))
      where
        -- the empty string, which the lowering makes a character's string
        -- from (`Cons` onto it), whether the body names it or not; an image
        -- leaves out a static nothing reaches
        plan : Constant -> Maybe (Name, StaticPlan)
        plan k = case intConst k of
          Just (Wide _, v) => let p = patternValue v in
                              if HeapObj.ValEnc.inFixnumRange p then Nothing else Just (int64Static p, Boxed p)
          Just (Unbounded, v) => if HeapObj.ValEnc.inFixnumRange v then Nothing else Just (bignumStatic v, Big v)
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
          -- a constant case compares with each alternative's constant, so a string
          -- among them needs its static as any constant does
          one (CONSTCASE _ alts d) acc =
            assert_total (maybe id go d (foldl (\(known, ss), alt => go (snd alt) (known, note (fst alt) ss)) acc alts))
          one _ acc = acc

    bodyStatics : (Name, VMDef) -> Maybe (SortedMap Name StaticPlan)
    bodyStatics (_, MkVMFun _ body) = Just (staticsOf body)
    bodyStatics _ = Nothing

    ready : (Name, StaticPlan) -> Maybe (s ** ({0 d : TermIR.Decls enc} -> TermIR.StaticDef d s))
    ready (n, Nullary c) = case choose (TermIR.FieldTys.wellFormed (Types.Header.ConH {enc} (cast c) 0)) of
      Left ok =>
        Just
          (TermIR.MkStaticSig n Types.Kind.CON ** TermIR.MkStaticDef
           (Types.Header.ConH (cast c) 0) [])
      Right _ => Nothing
    ready (n, Boxed p) =
      Just
        (TermIR.MkStaticSig n Types.Kind.INT64 ** TermIR.MkStaticDef Types.Header.Int64H
         [TermIR.StaticDef.SWord (cast p)])
    ready (n, Big v) = case Types.BignumEnc.signInHeader enc.bignum of
      Just sh => bigStatic n v sh (Types.BignumEnc.magnitudeWords (abs v))
      Nothing => Nothing
      where
        ||| A static object's declaration and definition, if its header can hold
        ||| it. Its words name nothing, so it is defined for any declarations.
        -- A big constant's static: a header of its sign and words.
        bigStatic : Name -> Integer -> (sh : Types.BignumEnc.SignInHeader enc.bignum) -> (ws : List Int64) ->
                    Maybe (s ** ({0 d : TermIR.Decls enc} -> TermIR.StaticDef d s))
        bigStatic n v sh ws =
          case choose (TermIR.FieldTys.wellFormed (Types.Header.BignumH {enc} @{sh} (v < 0) (length ws))) of
          Left ok =>
            Just
              (TermIR.MkStaticSig n Types.Kind.BIGNUM ** TermIR.MkStaticDef
               (Types.Header.BignumH @{sh} (v < 0) (length ws)) (map TermIR.StaticDef.SWord (fromList ws)))
          Right _ => Nothing
    ready (n, Text s) = do
      (h ** ws) <- Strings.literal enc s
      case choose (TermIR.FieldTys.wellFormed h) of
        Left ok =>
          Just
            (TermIR.MkStaticSig n Types.Kind.STRING ** TermIR.MkStaticDef h
             (map TermIR.StaticDef.SWord ws))
        Right _ => Nothing
