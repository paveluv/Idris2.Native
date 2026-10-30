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
||| routine the lowering calls, and the static objects: those a pass over
||| the bodies collects first, the nullary constructors and the integer
||| constants outside the fixnum range, those that casts of constants make
||| included, of the constants marked static read as literals too; and
||| those the constants the program marks static are read by, which their
||| reads name, with the objects those hold. A static's words are made once
||| the declarations are fixed, so that one holding another's address has
||| it from them (`DeferredStatic`).
|||
||| A constant the program marks static has its value computed as the
||| program is compiled (`Native.Codegen.StaticRead`), so ordinary code's
||| read of it, a call of no arguments in VMCode, is that value, as a
||| literal's is: no call and no cell. Its VMCode function, which computes
||| it, stays among the program's, but no ordinary code calls it, and the
||| image leaves it out. Flat code reads it as its value too
||| (`LowerFlat.flatRead`), where it holds it in one uniform register or as
||| a machine scalar, and calls its flat form, which computes it, where it
||| holds it otherwise.
|||
||| What v0 lowers: integer constants, those outside the fixnum range as
||| static objects; every integer type's arithmetic, bitwise operations,
||| shifts, division and comparisons, each wrapping to the type's width
||| ("Integers", below); double constants, as static objects, and doubles'
||| arithmetic, negation, square root, floor, ceiling and comparisons; the
||| casts Idris defines between primitive types (`Native.Codegen.CastWay`);
||| constructors, nullary ones as shared statics; closures; application;
||| calls and tail calls; cases on constructors, on integer and character
||| constants and on string constants; projection; the arrays behind
||| `Data.IOArray` ("Arrays", below) and the references behind `Data.IORef`
||| ("References"); the string primitives; and the foreign functions the
||| runtime implements. Everything else lowers to `Unsupported`, the abort
||| stub, so a program always links and fails only on the paths it reaches.
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
||| same static object. A type constructor built as a value is a
||| constructor whose id is its number among the program's (`typeCons`),
||| so one of no arguments is the static object of that id too.
module Native.Codegen.Lower

import Native.Codegen.CastWay
import Native.Codegen.ConstantWord
import Native.Codegen.Doubles
import Native.Codegen.IntWidth
import Native.Codegen.IRCommon.ConIds as IRCommon
import Native.Codegen.IRCommon.Conv
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Codegen.Linkage.ConvertsIn
import Native.Codegen.Linkage.Realised as Linkage
import Native.Codegen.Linkage.Routine
import Native.Codegen.Linkage.Sym
import Native.Codegen.LowerFlat
import Native.Codegen.Platform
import Native.Codegen.StaticRead
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
import Native.Area
import Native.Carrier
import Native.Data.Builder as Data
import Native.Data.Distinct
import Native.Data.Numbered
import Native.Field
import Native.Flat.Exp
import Native.HeapObj.Shape as HeapObj
import Native.HeapObj.ValEnc
import Native.Mach
import Native.Port
import Native.Rep
import Native.Types.BignumEnc as Types
import Native.Types.Enc as Types
import Native.Types.Header as Types
import Native.Types.IntegerRoutine as Types
import Native.Types.Kind
import Native.Types.StringRoutine as Types
import Native.Width

%default covering


------------------------------------------------------------------------------
-- Names the lowering introduces

||| The function the program starts with.
export
mainExpression : Name
mainExpression = MN "__mainExpression" 0

||| The function that computes a top-level constant's value, which the
||| constant's own name calls on its first use (`Constant`).
export
constantValue : Name -> Name
constantValue n = NS (mkNamespace "_native") (UN (Basic ("value of " ++ show n)))

------------------------------------------------------------------------------
-- Integers
--
-- Every integer type wraps to its width, as Idris's do, except `Integer`,
-- which is unbounded. In a uniform slot a narrow integer, of fewer than 64
-- bits, is always a fixnum. A 64-bit one is its bit pattern: a fixnum when the
-- pattern's signed value is in the fixnum range, and an `INT64` box holding
-- the pattern otherwise, so that the 64-bit types share one form and convert
-- among themselves for free. An `Integer` is a fixnum or a `BIGNUM`. How a
-- type is held is its width (`Native.Codegen.IntWidth`), by which a
-- constant of it is read too.
--
-- The locals are uniform, so an operation reads and writes uniform values. On
-- fixnums it works on the `Fix`es; otherwise, and when the result leaves the
-- fixnums, a narrow or 64-bit operation works on the words, a 64-bit result
-- being tagged if it fits and boxed if not, and an `Integer` operation calls
-- the runtime's routine on the original operands.

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

||| Each function and static of the declarations by name, with its variable,
||| the contract as the loaded runtime realises it, the type constructors'
||| ids (`IRCommon.ConIds`), and the constants the program marks static,
||| each as code reads it.
record Refs (enc : Types.Enc) (d : TermIR.Decls enc) where
  constructor MkRefs
  funs : SortedMap Name (s ** TermIR.Var d.sigs s)
  stats : SortedMap Name (s ** TermIR.Var d.statics s)
  realised : Linkage.Realised
  typeCons : SortedMap Name Int
  staticReads : SortedMap Name StaticRead

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
      -- lint: allow trust-escape: VMCode nests its instruction lists in tuples, which totality
      -- checking does not see through
      CASE s alts d => assert_total (union (union (altsRead alts) (maybe empty reads d)) (regs [s]))
      CONSTCASE s alts d =>
        assert_total (union (union (altsRead alts) (maybe empty reads d)) (regs [s]))
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
vals : (xs : List (TermIR.Opnd v IRCommon.Ty.Val)) ->
       All (TermIR.Opnd v) (replicate (length xs) IRCommon.Ty.Val)
vals [] = []
vals (x :: xs) = x :: vals xs

allVals : {n : Nat} -> All (TermIR.Opnd v) (replicate n IRCommon.Ty.Val) ->
          List (TermIR.Opnd v IRCommon.Ty.Val)
allVals {n = Z} [] = []
allVals {n = S n} (x :: xs) = x :: allVals xs

||| A function of the compiler's own library that walks a string
||| (`Libraries.Data.String.Iterator`), by its name. The lowering makes
||| these itself, of calls of string routines (`stringIterator`), so they
||| are among what may call routines (`calledRoutines`).
iterator : String -> Name
iterator s = NS (mkNamespace "Libraries.Data.String.Iterator") (UN (Basic s))

parameters {enc : Types.Enc} {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val}
           (0 d : TermIR.Decls enc) (refs : Refs enc d)
           {0 v : IRCommon.Ty enc -> Type} {0 l : List (IRCommon.Ty enc) -> Type}

  0 B : Type -> Type
  B = TermIR.Build d IRCommon.Conv.CPS False v l

  0 E : Type
  E = TermIR.Build.End d IRCommon.Conv.CPS False v l

  ------------------------------------------------------------------------------
  -- References

  ||| A static object of the program, as a `Val` (`LowerFlat.staticVal`).
  staticVal : Name -> B (TermIR.Opnd v IRCommon.Ty.Val)
  staticVal = LowerFlat.staticVal refs.stats

  ||| A word of the program (`ConstantWord.StaticWord`), as a `Val`: a fixnum
  ||| as an immediate, the erased value, a static object by its address
  ||| (`LowerFlat.staticWordVal`).
  staticWordVal : ConstantWord.StaticWord -> B (TermIR.Opnd v IRCommon.Ty.Val)
  staticWordVal = LowerFlat.staticWordVal {enc} refs.stats

  ||| A runtime routine's variable, with its results and parameters.
  routine : Name -> (rs, ps : List (IRCommon.Ty enc)) ->
            Maybe
            (n' ** TermIR.Var d.sigs
             (TermIR.MkSig n' (IRCommon.Conv.Direct rs False) ps False))
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
  strings : (c : Types.StringRoutine) ->
            All (TermIR.Opnd v) (Linkage.Routine.portParams (Types.StringRoutine.port c)) ->
            B (All (TermIR.Opnd v) (Linkage.Routine.portResults (Types.StringRoutine.port c)))
  strings c xs = case Linkage.Routine.stringRoutine refs.realised c of
    Just n => callRoutine n xs
    Nothing =>
      TermIR.Build.unsupported
        "a string operation, which the runtime has no module for under the encoding"

  ||| A double's value, from its box, a `DOUBLE` of one double, and the box of
  ||| one, which the program allocates: how ordinary code holds a double.
  valDouble : TermIR.Opnd v IRCommon.Ty.Val -> B (TermIR.Opnd v IRCommon.Ty.F64)
  valDouble x = do
    p <- TermIR.Build.emit1 (TermIR.Instr.NarrowPtr Types.Kind.DOUBLE x)
    TermIR.Build.emit1
      (TermIR.Instr.Load IRCommon.Ty.F64 (TermIR.MkMem (TermIR.Mem.AtPtr p) Nothing 8))

  doubleVal : TermIR.Opnd v IRCommon.Ty.F64 -> B (TermIR.Opnd v IRCommon.Ty.Val)
  doubleVal f = do
    p <- TermIR.Build.emit1 (TermIR.Instr.AllocObj Types.Header.DoubleH [f])
    TermIR.Build.emit1 (TermIR.Instr.WidenPtr p)

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
    TermIR.Build.emit1
      (TermIR.Instr.Load IRCommon.Ty.W64 (TermIR.MkMem (TermIR.Mem.AtPtr p) Nothing 8))

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
  constructor : Int -> (fields : List (TermIR.Opnd v IRCommon.Ty.Val)) ->
                B (TermIR.Opnd v IRCommon.Ty.Val)
  constructor conId fields =
    case choose
      (TermIR.FieldTys.wellFormed (Types.Header.ConH {enc} (cast conId) (length fields))) of
    Left ok => do
      p <- TermIR.Build.emit1
        (TermIR.Instr.AllocObj (Types.Header.ConH (cast conId) (length fields)) (vals fields))
      TermIR.Build.emit1 (TermIR.Instr.WidenPtr p)
    Right _ =>
      TermIR.Build.unsupported
        ("the constructor id " ++ show conId ++ ", which its header cannot hold")

  ------------------------------------------------------------------------------
  -- The boundary with flat code
  --
  -- A function that has a flat form (`Native.Codegen.LowerFlat`) is a
  -- wrapper around the form's `Direct` function: it takes its arguments
  -- apart into the form's registers, calls the form, and builds its result
  -- from the form's, as ordinary code represents each type
  -- (`Flat.Exp.Ordinary`).

  ||| The foreign functions of the compiler's own library that walk a string
  ||| (`Libraries.Data.String.Iterator`), lowered here, as Idris's JavaScript
  ||| code generator lowers them, since their types (`StringIterator`,
  ||| `UnconsResult`) are the compiler's library's, which the runtime does not
  ||| import. A stopgap: library knowledge in the code generator, until an
  ||| implementation can come from a package that names those types. An iterator is a
  ||| fixnum, the string encoding's position in the string (under UTF-8 a byte
  ||| offset, a step a character's bytes): `fromString` the first, 0;
  ||| `uncons` the character there and the position after it, `Character`
  ||| (tag 1, of the two), or `EOF` (tag 0) at the end; `withIteratorString`
  ||| the function, of its type's argument first, applied to the string from
  ||| the position on. Nothing for any other function.
  stringIterator : Name -> List (TermIR.Opnd v IRCommon.Ty.Val) -> Maybe E
  stringIterator n args =
    if n == iterator "fromString" then case args of
      [_] => map (\w => do x <- staticWordVal w; TermIR.Build.return x)
                 (ConstantWord.fixnumWord 0)
      _ => Nothing
    else if n == iterator "uncons" then case args of
      [str, it] => Just $ do
        at <- fixValue it
        [next] <- strings Types.StringRoutine.After [str, at]
        TermIR.Build.branch IRCommon.Op.EqR next at
          (do eof <- staticVal (ConstantWord.nullaryCon 0)
              TermIR.Build.return eof) $ do
          [c] <- strings Types.StringRoutine.CharAt [str, at]
          cv <- TermIR.Build.emit1 (TermIR.Instr.Tag c) >>= widen
          nv <- TermIR.Build.emit1 (TermIR.Instr.Tag next) >>= widen
          r <- constructor 1 [cv, nv]
          TermIR.Build.return r
      _ => Nothing
    else if n == iterator "withIteratorString" then case args of
      [_, str, it, f] => Just $ do
        at <- fixValue it
        [rest] <- strings Types.StringRoutine.From [str, at]
        TermIR.Build.tailApply f rest
      _ => Nothing
    else Nothing

  ||| A function that has a flat form: its arguments taken apart, the form
  ||| called, its result built.
  boundary : LowerFlat.Callee d -> (params : List Flat.Exp.Shape) -> (result : Flat.Exp.Shape) ->
             List (TermIR.Opnd v IRCommon.Ty.Val) -> E
  boundary (LowerFlat.MkCallee fd (_ ** var)) ss rs xs = do
    parts <- traverse (uncurry unbox) (zip ss xs)
    case LowerFlat.regsAs (LowerFlat.paramsLayout fd.params) (LowerFlat.concatValues parts) of
      Nothing =>
        TermIR.Build.unsupported
          ("arguments of other layouts for the flat form of " ++ show fd.name)
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
                   f <- valDouble x
                   pure (LowerFlat.MkValue [Rep.Dbl] [f])
        Flat.Exp.PrimShape WorldType => pure LowerFlat.noRegs
        Flat.Exp.PrimShape t => case IntWidth.intWidth t of
                   Just (IntWidth.Bounded (Width.Narrow _) _) => do
                     w <- fixValue x
                     pure (LowerFlat.MkValue [Rep.Word] [w])
                   Just (IntWidth.Bounded Width.Whole _) => do
                     w <- wideWord x
                     pure (LowerFlat.MkValue [Rep.Word] [w])
                   _ => TermIR.Build.unsupported ("a value of " ++ show t ++ " passed to flat code")
        Flat.Exp.UniformShape => pure (LowerFlat.MkValue [Rep.Uniform] [x])
        Flat.Exp.ByteAddrShape => TermIR.Build.unsupported "a byte address passed to flat code"
        Flat.Exp.DataShape [] => pure LowerFlat.noRegs
        Flat.Exp.DataShape [c] => LowerFlat.concatValues <$> fieldsFrom c x
        s@(Flat.Exp.DataShape cs) =>
          if all isTag cs then do t <- fixValue x
                                  pure (LowerFlat.MkValue [Rep.Word] [t]) else do
            let lay = Flat.Exp.shapeLayout s
            q <- TermIR.Build.emit1 (TermIR.Instr.NarrowPtr Types.Kind.CON x)
            i <- TermIR.Build.emit1 (TermIR.Instr.LoadPart Types.Header.ConIdP q)
            rs <- TermIR.Build.joinPoint (LowerFlat.tys lay) $ \done => do
              let branches = mapMaybe (\c => case (c.ordinary, LowerFlat.placement cs c.name) of
                                               (Flat.Exp.AsObject cid, Just (_, p)) =>
                                                 Just (the Int64 (cast cid), do
                                                          fs <- fieldsFrom c x
                                                          r <- LowerFlat.conValue p
                                                            (LowerFlat.concatValues fs)
                                                          maybe
                                                            (TermIR.Build.unsupported
                                                             "a sum of another layout")
                                                            done (LowerFlat.regsAs lay r))
                                               _ => Nothing) cs
              if length branches /= length cs
                then TermIR.Build.unsupported "a sum some of whose constructors are not objects"
                  else
                case choose
                  (Data.Distinct.distinct (map fst branches)
                   && TermIR.Body.keysFit (IRCommon.Ty.W64 {enc}) (map fst branches)) of
                  Left ok =>
                    TermIR.Build.switch i branches (TermIR.Build.crash "no constructor of the type")
                  Right _ => TermIR.Build.unsupported "a sum with repeated constructor ids"
            pure (LowerFlat.MkValue lay rs)
        where
          ||| The registers of the fields of an ordinary value of the constructor.
          fieldsFrom : Flat.Exp.ConShape -> TermIR.Opnd v IRCommon.Ty.Val ->
                       B (List (LowerFlat.Value enc v))
          fieldsFrom c x = case c.ordinary of
            Flat.Exp.AsTag => pure []
            -- the newtype's other fields, such as `MkIORes`'s world, take no
            -- registers
            Flat.Exp.AsField k =>
              traverse (\(j, s) => unbox s (if j == k then x else TermIR.Opnd.Erased))
                (Data.Numbered.numbered c.fields)
            Flat.Exp.AsObject _ => case c.fields of
                       [] => pure []
                       fs => do
                         q <- TermIR.Build.emit1 (TermIR.Instr.NarrowPtr Types.Kind.CON x)
                         traverse (\(j, s) => do f <- TermIR.Build.emit1
                                                   (TermIR.Instr.Load IRCommon.Ty.Val
                                                    (TermIR.MkMem (TermIR.Mem.AtPtr q) Nothing
                                                      (8 + 8 * cast j)))
                                                 unbox s f)
                                  (Data.Numbered.numbered fs)

      ||| The ordinary value of the shape, from its registers.
      box : Flat.Exp.Shape -> LowerFlat.Value enc v -> B (TermIR.Opnd v IRCommon.Ty.Val)
      box shape x = case shape of
        Flat.Exp.PrimShape DoubleType => case LowerFlat.valueDouble x of
                   Just f => doubleVal f
                   Nothing => TermIR.Build.unsupported "a double of another layout from flat code"
        Flat.Exp.PrimShape WorldType => pure TermIR.Opnd.Erased
        Flat.Exp.PrimShape t => case (IntWidth.intWidth t, LowerFlat.valueWord x) of
                   (Just (IntWidth.Bounded (Width.Narrow _) _), Just w) => do
                     f <- TermIR.Build.emit1 (TermIR.Instr.Tag w)
                     widen f
                   (Just (IntWidth.Bounded Width.Whole _), Just w) => wideVal w
                   _ =>
                     TermIR.Build.unsupported ("a value of " ++ show t ++ " returned by flat code")
        Flat.Exp.UniformShape => case x of
                   LowerFlat.MkValue [Rep.Uniform] [u] => pure u
                   _ => TermIR.Build.unsupported "a uniform value of another layout from flat code"
        Flat.Exp.ByteAddrShape => TermIR.Build.unsupported "a byte address returned by flat code"
        Flat.Exp.DataShape [] => pure TermIR.Opnd.Erased
        Flat.Exp.DataShape [c] => boxCon c x
        Flat.Exp.DataShape cs => case LowerFlat.valueTag x of
                   Nothing => TermIR.Build.unsupported "a sum without its tag from flat code"
                   Just t => if all isTag cs then do f <- TermIR.Build.emit1 (TermIR.Instr.Tag t)
                                                     widen f else do
                     [r] <- TermIR.Build.joinPoint [IRCommon.Ty.Val] $ \done => do
                       let branches = mapMaybe (\c => do (_, p) <- LowerFlat.placement cs c.name
                                                         fs <- LowerFlat.valueFields p x
                                                         pure (the Int64 (cast c.tag),
                                                               do r <- boxCon c fs; done [r]))
                                                           cs
                       if length branches /= length cs
                         then TermIR.Build.unsupported "a sum of another layout from flat code" else
                         case choose
                           (Data.Distinct.distinct (map fst branches)
                            && TermIR.Body.keysFit (IRCommon.Ty.W64 {enc}) (map fst branches)) of
                           Left ok =>
                             TermIR.Build.switch t branches
                               (TermIR.Build.crash "no constructor of the type")
                           Right _ => TermIR.Build.unsupported "a sum with repeated tags"
                     pure r
        where
          ||| The ordinary value of the constructor, from its fields' registers.
          boxCon : Flat.Exp.ConShape -> LowerFlat.Value enc v -> B (TermIR.Opnd v IRCommon.Ty.Val)
          boxCon c fs = case LowerFlat.splitBy (map Flat.Exp.shapeLayout c.fields) fs of
            Nothing =>
              TermIR.Build.unsupported ("the fields of " ++ show c.name ++ ", of another layout")
            Just xs => case c.ordinary of
              Flat.Exp.AsTag =>
                maybe (TermIR.Build.unsupported "a tag outside the fixnum range") staticWordVal
                  (ConstantWord.fixnumWord (cast c.tag))
              Flat.Exp.AsField k => case getAt k (zip c.fields xs) of
                         Just (s, f) => box s f
                         Nothing =>
                           TermIR.Build.unsupported
                             ("the newtype " ++ show c.name ++ " without its field")
              Flat.Exp.AsObject cid => case c.fields of
                         [] => staticVal (ConstantWord.nullaryCon cid)
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
        x <- staticVal (ConstantWord.nullaryCon conId)
        lower (set env r x) t is k
      (MKCON r (Left conId) args, _) :: is => do
        x <- constructor conId (map (get env) args)
        lower (set env r x) t is k
      (MKCON r (Right n) args, _) :: is => case lookup n refs.typeCons of
        Nothing =>
          TermIR.Build.unsupported ("the type constructor " ++ show n ++ ", which has no id")
        Just tid => do
          x <- case args of
                 [] => staticVal (ConstantWord.nullaryCon tid)
                 _ => constructor tid (map (get env) args)
          lower (set env r x) t is k
      (MKCLOSURE r f missing args, _) :: is =>
        case lookup f refs.funs of
          Just (TermIR.MkSig _ IRCommon.Conv.CPS _ _ ** code) => do
            x <- closure f code missing (map (get env) args)
            lower (set env r x) t is k
          _ =>
            TermIR.Build.unsupported
              ("a closure of " ++ show f ++ ", which is not a function of the program")
      (APPLY r f a, _) :: is =>
        if t && isNil is && isRVal r
           then TermIR.Build.tailApply (get env f) (get env a)
           else do
             x <- TermIR.Build.apply (get env f) (get env a)
             lower (set env r x) t is k
      (CALL r tl f args, _) :: is => case (args, lookup f refs.staticReads) of
        -- a read of a constant marked static is its value, in tail position
        -- too: a tail call is the last instruction, and the rest returns it
        ([], Just rd) => do
          env' <- readStatic env r rd
          lower env' t is k
        _ => case cpsFunction f (length (map (get env) args)) of
          Nothing =>
            TermIR.Build.unsupported
              ("a call to " ++ show f ++ ", which is not a function of the program")
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
        case traverse (either Just (\n => lookup n refs.typeCons) . fst) alts of
          Nothing => TermIR.Build.unsupported "a case on a type constructor that has no id"
          Just ids => do
            q <- TermIR.Build.emit1 (TermIR.Instr.NarrowPtr Types.Kind.CON (get env s))
            i <- TermIR.Build.emit1 (TermIR.Instr.LoadPart Types.Header.ConIdP q)
            cases env after t is k (map snd alts)
              (fromMaybe [ERROR "no case alternative matched"] dflt) $
              \codes, other => onKeys i (zip (map cast ids) codes) other
      (CONSTCASE s alts dflt, after) :: is =>
        case (traverse (ConstantWord.intConst . fst) alts, traverse (text . fst) alts) of
          (Just ks, _) =>
            cases env after t is k (map snd alts)
              (fromMaybe [ERROR "no case alternative matched"] dflt) $
              \codes,
                other => constCase (get env s) (zip (map snd ks) codes) (map fst (head' ks)) other
          (Nothing, Just ts) =>
            cases env after t is k (map snd alts)
              (fromMaybe [ERROR "no case alternative matched"] dflt) $
              \codes, other => stringCase (get env s) (zip ts codes) other
          (Nothing, Nothing) => TermIR.Build.unsupported "a case on doubles"
      (PROJECT r x i, _) :: is => do
        q <- TermIR.Build.emit1 (TermIR.Instr.NarrowPtr Types.Kind.CON (get env x))
        f <- TermIR.Build.emit1
          (TermIR.Instr.Load IRCommon.Ty.Val
            (TermIR.MkMem (TermIR.Mem.AtPtr q) Nothing (8 + 8 * i)))
        lower (set env r f) t is k
      (ERROR msg, _) :: _ => TermIR.Build.crash msg
      where
        ||| A closure of the function, with the arguments filled and `missing` to
        ||| come, its header decided here.
        closure : Name -> TermIR.Var d.sigs (TermIR.MkSig n IRCommon.Conv.CPS ps cv) ->
                  (missing : Nat) ->
                  (args : List (TermIR.Opnd v IRCommon.Ty.Val)) -> B (TermIR.Opnd v IRCommon.Ty.Val)
        closure f code missing args =
          case choose
            (TermIR.FieldTys.wellFormed
              (Types.Header.ClosureH {enc} (missing + length args) (length args))) of
            Left ok => do
              c <- TermIR.Build.emit1 (TermIR.Instr.CodeOf code)
              p <- TermIR.Build.emit1
                (TermIR.Instr.AllocObj (Types.Header.ClosureH (missing + length args) (length args))
                  (c :: vals args))
              TermIR.Build.emit1 (TermIR.Instr.WidenPtr p)
            Right _ =>
              TermIR.Build.unsupported ("a closure of " ++ show f ++ " that its header cannot hold")

        isRVal : Reg -> Bool
        isRVal RVal = True
        isRVal _ = False

        ||| A CPS function of the program of `n` parameters.
        cpsFunction : Name -> (n : Nat) ->
                      Maybe
                      (nm ** cv ** TermIR.Var d.sigs
                       (TermIR.MkSig nm IRCommon.Conv.CPS (replicate n IRCommon.Ty.Val) cv))
        cpsFunction name n = case lookup name refs.funs of
          Just (TermIR.MkSig nm IRCommon.Conv.CPS ps cv ** var) =>
            case decEq ps (replicate n IRCommon.Ty.Val) of
            Yes Refl => Just (nm ** cv ** var)
            No _ => Nothing
          _ => Nothing

        set : Env v -> Reg -> TermIR.Opnd v IRCommon.Ty.Val -> Env v
        set env r x = maybe env (\k => insert k (x, Nothing) env) (key r)

        extPrim : Env v -> Reg -> Name -> List Reg -> B (Env v)
        extPrim env r p list =
          if p == arrayPrim "prim__newArray" then case list of
            [_, x, y, _] => do count <- wideWord (get env x)
                               a <- TermIR.Build.emit1
                                 (TermIR.Instr.AllocSized Types.Header.ArrayElemsP count
                                   (get env y))
                               set env r <$> TermIR.Build.emit1 (TermIR.Instr.WidenPtr a)
            _ => notLowered
          else if p == arrayPrim "prim__arrayGet" then case list of
            [_, x, y, _] => do a <- TermIR.Build.emit1
                                 (TermIR.Instr.NarrowPtr Types.Kind.ARRAY (get env x))
                               i <- wideWord (get env y)
                               set env r <$> TermIR.Build.emit1
                                 (TermIR.Instr.Load IRCommon.Ty.Val
                                   (TermIR.MkMem (TermIR.Mem.AtPtr a) (Just i) 8))
            _ => notLowered
          -- The result is `()`, which no caller inspects: the erased value.
          else if p == arrayPrim "prim__arraySet" then case list of
            [_, x, y, z, _] => do a <- TermIR.Build.emit1
                                    (TermIR.Instr.NarrowPtr Types.Kind.ARRAY (get env x))
                                  i <- wideWord (get env y)
                                  TermIR.Build.emit0
                                    (TermIR.Instr.Store IRCommon.Ty.Val
                                      (TermIR.MkMem (TermIR.Mem.AtPtr a) (Just i) 8)
                                     (get env z))
                                  pure (set env r TermIR.Opnd.Erased)
            _ => notLowered
          else if p == refPrim "prim__newIORef" then case list of
            [_, x, _] => do a <- TermIR.Build.emit1
                              (TermIR.Instr.AllocObj Types.Header.IORefH [get env x])
                            set env r <$> TermIR.Build.emit1 (TermIR.Instr.WidenPtr a)
            _ => notLowered
          else if p == refPrim "prim__readIORef" then case list of
            [_, x, _] => do a <- TermIR.Build.emit1
                              (TermIR.Instr.NarrowPtr Types.Kind.IOREF (get env x))
                            set env r <$> TermIR.Build.emit1
                              (TermIR.Instr.Load IRCommon.Ty.Val
                                (TermIR.MkMem (TermIR.Mem.AtPtr a) Nothing 8))
            _ => notLowered
          -- The result is `()`, as an array's write's.
          else if p == refPrim "prim__writeIORef" then case list of
            [_, x, y, _] => do a <- TermIR.Build.emit1
                                 (TermIR.Instr.NarrowPtr Types.Kind.IOREF (get env x))
                               TermIR.Build.emit0
                                 (TermIR.Instr.Store IRCommon.Ty.Val
                                   (TermIR.MkMem (TermIR.Mem.AtPtr a) Nothing 8) (get env y))
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
        cases : Env v -> (after : SortedSet Int) -> (tail : Bool) -> List (VMInst, SortedSet Int) ->
                (Env v -> E) ->
                (alts : List (List VMInst)) -> (dflt : List VMInst) -> (List E -> E -> E) -> E
        cases env after True [] k alts dflt dispatch =
          dispatch (map (\alt => lower env True (annotate after alt) k) alts)
            (lower env True (annotate after dflt) k)
        cases env after t is k alts dflt dispatch = do
          -- the locals the alternatives assign that the rest reads: each of the
          -- few assigned looked up in what is read after, which is as long as the
          -- rest of the function (`intersection` walks its second set)
          let ks = filter (\r => contains r after)
                          (Prelude.toList
                            (foldr (\alt, w => union w (writes alt)) (writes dflt) alts))
              kset = fromList ks
              exitWith : TermIR.Build.Jumper d IRCommon.Conv.CPS False v l
                         (replicate (length ks) IRCommon.Ty.Val) ->
                         Env v -> E
              exitWith exit e = exit (passed e ks)
          vals <- TermIR.Build.joinPoint (replicate (length ks) IRCommon.Ty.Val) $ \exit =>
            dispatch (map (\alt => lower env False (annotate kset alt) (exitWith exit)) alts)
                     (lower env False (annotate kset dflt) (exitWith exit))
          lower (foldl (\e, (k', x) => insert k' (x, Nothing) e) env (zip ks (allVals vals))) t is k
          where
            -- A local an alternative leaves as it was passes on as it was; one it
            -- never had passes on as the erased value, which no path reads.
            passed : Env v -> (ks : List Int) ->
                     All (TermIR.Opnd v) (replicate (length ks) IRCommon.Ty.Val)
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
                -- lint: allow trust-escape: VMCode nests its instruction lists in tuples, which
                -- totality checking does not see through
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
            (Data.Distinct.distinct (map fst cs)
              && TermIR.Body.keysFit (IRCommon.Ty.W64 {enc}) (map fst cs)) of
          Left ok => TermIR.Build.switch x cs other
          Right _ => TermIR.Build.unsupported "a case with repeated constructor ids"

        ||| A case on integer or character constants. A 64-bit scrutinee is
        ||| matched as a fixnum against the cases in the fixnum range and as a box
        ||| against the others; an `Integer` that is a `BIGNUM` matches no case in
        ||| the fixnum range.
        constCase : TermIR.Opnd v IRCommon.Ty.Val -> List (Integer, E) -> Maybe IntWidth -> E -> E
        constCase x cs y other = case y of
          Just (IntWidth.Bounded Width.Whole _) => do
            -- each alternative is reached from both switches, so it is a block
            alts <- traverse
              (\(n, code) => do j <- TermIR.Build.block [] (\[] => code)
                                pure (ConstantWord.patternValue n, j)) cs
            dflt <- TermIR.Build.block [] (\[] => other)
            TermIR.Build.ifFixnums [x]
              (\[f] =>
                onFixnums f [(cast p, j []) | (p, j) <- alts, HeapObj.ValEnc.inFixnumRange p]
                (dflt []))
              (case [(cast p, j []) | (p, j) <- alts, not (HeapObj.ValEnc.inFixnumRange p)] of
                 [] => dflt []
                 big => do w <- boxWord x; onKeys w big (dflt []))
          Just IntWidth.Unbounded => do
            dflt <- TermIR.Build.block [] (\[] => other)
            TermIR.Build.ifFixnums [x]
              (\[f] =>
                onFixnums f [(cast n, code) | (n, code) <- cs, HeapObj.ValEnc.inFixnumRange n]
                (dflt []))
              (if all (HeapObj.ValEnc.inFixnumRange . fst) cs
                  then dflt []
                  else TermIR.Build.unsupported
                    "a case on an Integer constant outside the fixnum range")
          _ => do
            f <- asFix x
            onFixnums f [(cast n, code) | (n, code) <- cs] other
          where
            ||| A switch on a fixnum, its keys decided here to be distinct fixnums.
            onFixnums : TermIR.Opnd v IRCommon.Ty.Fix -> List (Int64, E) -> E -> E
            onFixnums x cs other =
              case choose
                (Data.Distinct.distinct (map fst cs)
                  && TermIR.Body.keysFit (IRCommon.Ty.Fix {enc}) (map fst cs)) of
              Left ok => TermIR.Build.switch x cs other
              Right _ => TermIR.Build.unsupported "a case with repeated constants"

        setKnown : Env v -> Reg -> TermIR.Opnd v IRCommon.Ty.Val -> Constant -> Env v
        setKnown env r x c = maybe env (\k => insert k (x, Just c) env) (key r)

        ||| A constant as the value it is, by its word
        ||| (`ConstantWord.constantWord`); one that is no value under the
        ||| encoding is the abort stub, with the reason.
        constant : Constant -> B (TermIR.Opnd v IRCommon.Ty.Val)
        constant k =
          either TermIR.Build.unsupported (staticWordVal . fst)
            (ConstantWord.constantWord enc.bignum k)

        ||| A read of a constant the program marks static into the register,
        ||| and the environment after it: a literal as the constant it is,
        ||| which a cast of it folds, as a `MKCONSTANT`'s; the erased value;
        ||| or a static object's address. Nothing is called.
        readStatic : Env v -> Reg -> StaticRead -> B (Env v)
        readStatic env r (StaticRead.Literal c) = do x <- constant c; pure (setKnown env r x c)
        readStatic env r StaticRead.Erased = pure (set env r TermIR.Opnd.Erased)
        readStatic env r (StaticRead.Object n) = set env r <$> staticVal n

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

        ||| A call of an `Integer` routine of the program's encoding, of its port's
        ||| registers.
        integers : (c : Types.IntegerRoutine) ->
                   All (TermIR.Opnd v) (Linkage.Routine.portParams (Types.IntegerRoutine.port c)) ->
                   B (All (TermIR.Opnd v)
                      (Linkage.Routine.portResults (Types.IntegerRoutine.port c)))
        integers c xs = case Linkage.Routine.integerRoutine refs.realised c of
          Just n => callRoutine n xs
          Nothing =>
            TermIR.Build.unsupported
              "an Integer operation beyond the fixnums, which the runtime has none of yet"

        ||| A primitive operation, and the environment after it.
        op : Env v -> Reg -> PrimFn n -> Vect n Reg -> B (Env v)
        op env r fn' vect = case (fn', vect) of
          (Cast from to, [x]) => case CastWay.castWay from to of
            CastWay.Retype wf wt => foldedCast to x (retype wf wt)
            CastWay.ToChar wf => foldedCast to x (toChar wf)
            CastWay.IntToDouble wf => set env r <$> toDouble wf (get env x)
            CastWay.DoubleToInt wt => set env r <$> fromDouble wt (get env x)
            CastWay.CharString => do
              w <- fixValue (get env x)
              empty <- constant (Str "")
              [c] <- strings Types.StringRoutine.Cons [w, empty]
              pure (set env r c)
            CastWay.Decimal wf => set env r <$> decimal wf (get env x)
            CastWay.ReadInteger wt => do
              c <- case wt of
                IntWidth.Bounded (Width.Narrow n) s => do
                  [w] <- strings Types.StringRoutine.ReadWord [get env x]
                  narrowVal n s w
                IntWidth.Bounded Width.Whole _ => do
                  [w] <- strings Types.StringRoutine.ReadWord [get env x]
                  wideVal w
                IntWidth.Unbounded => do
                  [i] <- integers Types.IntegerRoutine.FromDecimal [get env x]
                  pure i
              pure (set env r c)
            CastWay.ShowDouble => do
              f <- valDouble (get env x)
              [t] <- strings Types.StringRoutine.ShowDouble [f]
              pure (set env r t)
            CastWay.ReadDouble => do
              [f] <- strings Types.StringRoutine.ReadDouble [get env x]
              d <- doubleVal f
              pure (set env r d)
            CastWay.NoCast =>
              TermIR.Build.unsupported ("the cast from " ++ show from ++ " to " ++ show to)
          (BelieveMe, [_, _, x]) => pure (set env r (get env x))
          (fn, args) => set env r <$> value fn args
          where
            ||| A cast to an integer type or to `Char` of the value in the
            ||| register, and the environment after it: the constant the cast
            ||| gives, made while compiling, when the value is a known integer
            ||| constant (`castConstant`); otherwise the code given, of the value.
            foldedCast : PrimType -> Reg ->
                         (TermIR.Opnd v IRCommon.Ty.Val -> B (TermIR.Opnd v IRCommon.Ty.Val)) ->
                         B (Env v)
            foldedCast to x code =
              case known env x >>= ConstantWord.intConst >>= (castConstant to . snd) of
                Just folded => do c <- constant folded; pure (setKnown env r c folded)
                Nothing => do c <- code (get env x); pure (set env r c)

            ||| A cast to `Char`: the value if it is a Unicode scalar value, 0 if not.
            toChar : IntWidth -> TermIR.Opnd v IRCommon.Ty.Val -> B (TermIR.Opnd v IRCommon.Ty.Val)
            toChar wf x = do
              w <- case wf of
                IntWidth.Bounded (Width.Narrow _) _ => fixValue x
                IntWidth.Bounded Width.Whole _ => wideWord x
                IntWidth.Unbounded => do
                  [w] <- TermIR.Build.joinPoint [IRCommon.Ty.W64] $ \done =>
                    TermIR.Build.ifFixnums [x] (\[f] => do w <- untag (f); done [w])
                      (done [TermIR.Opnd.W (-1)])
                  pure w
              [r] <- TermIR.Build.joinPoint [IRCommon.Ty.Val] $ \done => do
                keep <- TermIR.Build.block [] $ \[] => do f <- TermIR.Build.emit1
                                                            (TermIR.Instr.Tag w)
                                                          r <- widen f
                                                          done [r]
                zero <- TermIR.Build.block [] $ \[] => done [TermIR.Opnd.Vx {enc} 0]
                TermIR.Build.branch IRCommon.Op.LtS w (TermIR.Opnd.W 0) (zero []) $
                  TermIR.Build.branch IRCommon.Op.LeS w (TermIR.Opnd.W 55295) (keep []) $
                    TermIR.Build.branch IRCommon.Op.LtS w (TermIR.Opnd.W 57344) (zero []) $
                      TermIR.Build.branch IRCommon.Op.LeS w (TermIR.Opnd.W 1114111) (keep [])
                        (zero [])
              pure r

            ||| A word wrapped to a narrow width, as a uniform value: a fixnum, which it
            ||| always fits.
            narrowVal : Width.SubWord -> Bool -> TermIR.Opnd v IRCommon.Ty.W64 ->
                        B (TermIR.Opnd v IRCommon.Ty.Val)
            narrowVal n s w = do
              e <- TermIR.Build.emit1 (TermIR.Instr.Ext n s w)
              f <- TermIR.Build.emit1 (TermIR.Instr.Tag e)
              widen f

            ||| An integer of the width as the nearest double, ties to even.
            toDouble : IntWidth -> TermIR.Opnd v IRCommon.Ty.Val ->
                       B (TermIR.Opnd v IRCommon.Ty.Val)
            toDouble (IntWidth.Bounded (Width.Narrow n) s) x = do
              w <- fixValue x
              Doubles.fromWord (Width.Narrow n, s) w >>= doubleVal
            toDouble (IntWidth.Bounded Width.Whole s) x = do
              w <- wideWord x
              Doubles.fromWord (Width.Whole, s) w >>= doubleVal
            toDouble IntWidth.Unbounded x = do
              [f] <- TermIR.Build.joinPoint [IRCommon.Ty.F64] $ \done =>
                TermIR.Build.ifFixnums [x]
                  (\[a] => do w <- untag a
                              f <- TermIR.Build.emit1 (TermIR.Instr.Convert IRCommon.Op.I2F w)
                              done [f])
                  (do [f] <- integers Types.IntegerRoutine.ToDouble [x]
                      done [f])
              doubleVal f

            ||| A double as the integer type of the width: truncated, wrapped
            ||| (`Native.Codegen.Doubles`).
            fromDouble : IntWidth -> TermIR.Opnd v IRCommon.Ty.Val ->
                         B (TermIR.Opnd v IRCommon.Ty.Val)
            fromDouble (IntWidth.Bounded (Width.Narrow n) s) x = do
              f <- valDouble x
              w <- Doubles.toWord (Width.Narrow n, s) f
              narrowVal n s w
            fromDouble (IntWidth.Bounded Width.Whole s) x = do
              f <- valDouble x
              w <- Doubles.toWord (Width.Whole, s) f
              wideVal w
            fromDouble IntWidth.Unbounded x = do
              f <- valDouble x
              [i] <- integers Types.IntegerRoutine.FromDouble [f]
              pure i

            ||| A uniform integer of one width as one of another, wrapping as Idris's
            ||| casts do.
            retype : IntWidth -> IntWidth -> TermIR.Opnd v IRCommon.Ty.Val ->
                     B (TermIR.Opnd v IRCommon.Ty.Val)
            retype wf wt x =
              if keeps wf wt then pure x else case (wf, wt) of
                (IntWidth.Bounded (Width.Narrow _) _,
                  IntWidth.Bounded (Width.Narrow n) s) => fixValue x >>= narrowVal n s
                (IntWidth.Bounded Width.Whole _, IntWidth.Bounded (Width.Narrow n) s) =>
                  wideWord x >>= narrowVal n s
                (IntWidth.Unbounded, IntWidth.Bounded (Width.Narrow n) s) =>
                  integerBits x >>= narrowVal n s
                (IntWidth.Unbounded, IntWidth.Bounded Width.Whole _) => do
                  [r] <- TermIR.Build.joinPoint [IRCommon.Ty.Val] $ \done =>
                    TermIR.Build.ifFixnums [x] (\_ => done [x])
                      (do a <- integerBits x; r <- wideVal a; done [r])
                  pure r
                (IntWidth.Bounded Width.Whole True, IntWidth.Unbounded) => do
                  [r] <- TermIR.Build.joinPoint [IRCommon.Ty.Val] $ \done =>
                    TermIR.Build.ifFixnums [x] (\_ => done [x])
                      (do a <- boxWord x
                          [r] <- integers Types.IntegerRoutine.FromInt64 [a]
                          done [r])
                  pure r
                (IntWidth.Bounded Width.Whole False, IntWidth.Unbounded) => do
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
                keeps (IntWidth.Bounded Width.Whole _) (IntWidth.Bounded Width.Whole _) = True
                keeps (IntWidth.Bounded (Width.Narrow _) _) (IntWidth.Bounded Width.Whole _) = True
                keeps (IntWidth.Bounded (Width.Narrow _) _) IntWidth.Unbounded = True
                keeps IntWidth.Unbounded IntWidth.Unbounded = True
                keeps (IntWidth.Bounded (Width.Narrow n) s) (IntWidth.Bounded (Width.Narrow m) t) =
                  let a = Width.subWordBytes n
                      b = Width.subWordBytes m
                  in if s == t then b >= a else not s && t && b > a
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
            wordFix w = do f <- TermIR.Build.emit1 (TermIR.Instr.Tag w)
                           TermIR.Build.emit1 (TermIR.Instr.WidenFix f)

            ||| A word in decimal, signed or not, by the string routine for it.
            decimalWord : Bool -> TermIR.Opnd v IRCommon.Ty.W64 -> B (TermIR.Opnd v IRCommon.Ty.Val)
            decimalWord True w = do [t] <- strings Types.StringRoutine.ShowSigned [w]; pure t
            decimalWord False w = do [t] <- strings Types.StringRoutine.ShowUnsigned [w]; pure t

            ||| A number of the width in decimal, by its word; an `Integer` outside
            ||| the fixnums by the bignum encoding's routine.
            decimal : IntWidth -> TermIR.Opnd v IRCommon.Ty.Val -> B (TermIR.Opnd v IRCommon.Ty.Val)
            decimal (IntWidth.Bounded (Width.Narrow _) signed) x = do
              w <- fixValue x
              decimalWord signed w
            decimal (IntWidth.Bounded Width.Whole signed) x = do
              w <- wideWord x
              decimalWord signed w
            decimal IntWidth.Unbounded x = do
              [t] <- TermIR.Build.joinPoint [IRCommon.Ty.Val] $ \done =>
                TermIR.Build.ifFixnums [x] (\[f] => do w <- untag f
                                                       t <- decimalWord True w
                                                       done [t])
                  (do [t] <- integers Types.IntegerRoutine.ToDecimal [x]
                      done [t])
              pure t

            ||| A comparison of strings: the runtime's order, -1, 0 or 1, against 0.
            stringOrder : IRCommon.Op.Rel -> TermIR.Opnd v IRCommon.Ty.Val ->
                          TermIR.Opnd v IRCommon.Ty.Val ->
                          B (TermIR.Opnd v IRCommon.Ty.Val)
            stringOrder rel x y = do
              [o] <- strings Types.StringRoutine.Compare [x, y]
              b <- TermIR.Build.emit1 (TermIR.Instr.Cmp rel o (TermIR.Opnd.W 0))
              wordFix b

            ||| A call of an `Integer` routine on values that gives one, chosen as the
            ||| program is compiled: its operands and its result as its port's
            ||| registers.
            integerCall : Types.IntegerRoutine -> List (TermIR.Opnd v IRCommon.Ty.Val) ->
                          B (TermIR.Opnd v IRCommon.Ty.Val)
            integerCall c xs =
              case (Linkage.Routine.integerRoutine refs.realised c,
                    operands (Linkage.Routine.portParams (Types.IntegerRoutine.port c)) xs) of
              (Nothing, _) =>
                TermIR.Build.unsupported
                  "an Integer operation beyond the fixnums, which the runtime has none of yet"
              (Just name, Just os) => do
                rs <- callRoutine name
                  {rs = Linkage.Routine.portResults (Types.IntegerRoutine.port c)} os
                maybe
                  (TermIR.Build.crash ("the Integer routine " ++ show name ++ " gives no value"))
                    pure (one rs)
              (Just name, Nothing) =>
                TermIR.Build.crash ("the Integer routine " ++ show name ++ " takes other operands")
              where

                operands : (ts : List (IRCommon.Ty enc)) -> List (TermIR.Opnd v IRCommon.Ty.Val) ->
                           Maybe (All (TermIR.Opnd v) ts)
                operands [] [] = Just []
                operands (IRCommon.Ty.Val :: ts) (x :: more) = (x ::) <$> operands ts more
                operands _ _ = Nothing

                one : {ts : List (IRCommon.Ty enc)} -> All (TermIR.Opnd v) ts ->
                      Maybe (TermIR.Opnd v IRCommon.Ty.Val)
                one {ts = [IRCommon.Ty.Val]} [r] = Just r
                one _ = Nothing

            negation : IntWidth -> TermIR.Opnd v IRCommon.Ty.Val ->
                       B (TermIR.Opnd v IRCommon.Ty.Val)
            negation (IntWidth.Bounded (Width.Narrow n) s) x = do
              a <- fixValue x
              w <- TermIR.Build.emit1 (TermIR.Instr.Unary IRCommon.Op.Negate a)
              narrowVal n s w
            negation (IntWidth.Bounded Width.Whole _) x = do
              [r] <- TermIR.Build.joinPoint [IRCommon.Ty.Val] $ \done => do
                word <- TermIR.Build.block [IRCommon.Ty.W64] $ \[wa] => do
                  w <- TermIR.Build.emit1 (TermIR.Instr.Unary IRCommon.Op.Negate wa)
                  r <- wideVal w
                  done [r]
                TermIR.Build.ifFixnums [x]
                  (\[a] =>
                    TermIR.Build.arithOv TermIR.OvOp.OvSub (TermIR.Opnd.Fx 0) a
                    (\f => do r <- widen f; done [r])
                             (do wa <- untag (a); word [wa]))
                  (do wa <- wideWord x; word [wa])
              pure r
            negation IntWidth.Unbounded x = do
              [r] <- TermIR.Build.joinPoint [IRCommon.Ty.Val] $ \done => do
                slow <- TermIR.Build.block [] $ \[] => do r <- integerCall Types.IntegerRoutine.Neg
                                                            [x]
                                                          done [r]
                TermIR.Build.ifFixnums [x]
                  (\[a] =>
                    TermIR.Build.arithOv TermIR.OvOp.OvSub (TermIR.Opnd.Fx 0) a
                      (\f => do r <- widen f; done [r])
                   (slow []))
                    (slow [])
              pure r

            ||| `div` or `mod`.
            division : IntWidth -> (remainder : Bool) -> (x, y : TermIR.Opnd v IRCommon.Ty.Val) ->
                       B (TermIR.Opnd v IRCommon.Ty.Val)
            division (IntWidth.Bounded (Width.Narrow n) s) m x y = do
              a <- fixValue x
              b <- fixValue y
              Words.nonZero b
              w <- Words.divide s m a b
              narrowVal n s w
            division (IntWidth.Bounded Width.Whole s) m x y = do
              a <- wideWord x
              b <- wideWord y
              Words.nonZero b
              w <- Words.divide s m a b
              wideVal w
            division IntWidth.Unbounded m x y = do
              [r] <- TermIR.Build.joinPoint [IRCommon.Ty.Val] $ \done => do
                slow <- TermIR.Build.block [] $ \[] => do r <- integerCall
                                                            (if m then Types.IntegerRoutine.Mod
                                                             else Types.IntegerRoutine.Div)
                                                              [x, y]
                                                          done [r]
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
            shifting (IntWidth.Bounded (Width.Narrow n) s) left x y = do
              a <- fixValue x
              k <- fixValue y
              w <- Words.shiftBy
                (if left then IRCommon.Op.Shl else if s then IRCommon.Op.Sar else IRCommon.Op.Shr) a
                  k
              narrowVal n s w
            shifting (IntWidth.Bounded Width.Whole s) left x y = do
              a <- wideWord x
              k <- wideWord y
              w <- Words.shiftBy
                (if left then IRCommon.Op.Shl else if s then IRCommon.Op.Sar else IRCommon.Op.Shr) a
                  k
              wideVal w
            shifting IntWidth.Unbounded left x y = do
              [r] <- TermIR.Build.joinPoint [IRCommon.Ty.Val] $ \done => do
                slow <- TermIR.Build.block [] $ \[] => do r <- integerCall
                                                            (if left then Types.IntegerRoutine.Shl
                                                             else Types.IntegerRoutine.Shr)
                                                              [x, y]
                                                          done [r]
                TermIR.Build.ifFixnums [x, y]
                  (\[fa, fk] => do
                     a <- untag (fa)
                     k <- untag (fk)
                     TermIR.Build.branch IRCommon.Op.LtS k (TermIR.Opnd.W 0) (slow []) $
                       if left
                          then -- shift by at most 62, and keep the result only if
                               -- shifting back gives the operand and it is a fixnum
                               TermIR.Build.branch IRCommon.Op.GtS k (TermIR.Opnd.W 62) (slow []) $
                                 do
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
            withWidth ty what k = case IntWidth.intWidth ty of
              Just w => k w
              Nothing => TermIR.Build.unsupported (what ++ " on " ++ show ty)

            ||| Addition, subtraction, multiplication and the bitwise operations, with
            ||| the operation's `Integer` routine.
            arithmetic : IntWidth -> IRCommon.Op.ArithOp -> (routine : Types.IntegerRoutine) ->
                         (x, y : TermIR.Opnd v IRCommon.Ty.Val) -> B (TermIR.Opnd v IRCommon.Ty.Val)
            arithmetic width o routine x y = case width of
              IntWidth.Bounded (Width.Narrow n) s => do
                a <- fixValue x
                b <- fixValue y
                w <- TermIR.Build.emit1 (TermIR.Instr.Arith o a b)
                narrowVal n s w
              IntWidth.Bounded Width.Whole _ => do
                [r] <- TermIR.Build.joinPoint [IRCommon.Ty.Val] $ \done => do
                  words <- TermIR.Build.block [IRCommon.Ty.W64, IRCommon.Ty.W64] $ \[wa, wb] => do
                    w <- TermIR.Build.emit1 (TermIR.Instr.Arith o wa wb)
                    r <- wideVal w
                    done [r]
                  TermIR.Build.ifFixnums [x, y]
                    (\[a, b] => case ovOp o of
                       Just ov => TermIR.Build.arithOv ov a b (\f => do r <- widen f; done [r])
                                    (do wa <- untag (a); wb <- untag (b); words [wa, wb])
                       Nothing => do f <- TermIR.Build.emit1 (TermIR.Instr.Arith o a b)
                                     r <- widen f
                                     done [r])
                    (do wa <- wideWord x; wb <- wideWord y; words [wa, wb])
                pure r
              IntWidth.Unbounded => do
                [r] <- TermIR.Build.joinPoint [IRCommon.Ty.Val] $ \done => do
                  slow <- TermIR.Build.block [] $ \[] => do r <- integerCall routine [x, y]
                                                            done [r]
                  TermIR.Build.ifFixnums [x, y]
                    (\[a, b] => case ovOp o of
                       Just ov =>
                         TermIR.Build.arithOv ov a b (\f => do r <- widen f; done [r]) (slow [])
                       Nothing => do f <- TermIR.Build.emit1 (TermIR.Instr.Arith o a b)
                                     r <- widen f
                                     done [r])
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
              IntWidth.Bounded (Width.Narrow _) _ => do
                a <- asFix x
                b <- asFix y
                c <- TermIR.Build.emit1 (TermIR.Instr.Cmp rel a b)
                boolVal c
              IntWidth.Bounded Width.Whole s => do
                let rel' = if s then rel else unsignedRel rel
                [c] <- TermIR.Build.joinPoint [IRCommon.Ty.W64] $ \done =>
                  TermIR.Build.ifFixnums [x, y]
                    (\[a, b] => do c <- TermIR.Build.emit1 (TermIR.Instr.Cmp rel' a b); done [c])
                    (do a <- wideWord x
                        b <- wideWord y
                        c <- TermIR.Build.emit1 (TermIR.Instr.Cmp rel' a b)
                        done [c])
                boolVal c
              IntWidth.Unbounded => do
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

            ||| An arithmetic operation of two doubles, IEEE 754's, and a
            ||| comparison of two, false where either is NaN but `/=`.
            doubleArith : IRCommon.Op.FOp -> (x, y : Reg) -> B (TermIR.Opnd v IRCommon.Ty.Val)
            doubleArith o x y = do
              a <- valDouble (get env x)
              b <- valDouble (get env y)
              f <- TermIR.Build.emit1 (TermIR.Instr.FArith o a b)
              doubleVal f

            doubleOrder : IRCommon.Op.Rel -> (x, y : Reg) -> B (TermIR.Opnd v IRCommon.Ty.Val)
            doubleOrder rel x y = do
              a <- valDouble (get env x)
              b <- valDouble (get env y)
              c <- TermIR.Build.emit1 (TermIR.Instr.FCmp rel a b)
              TermIR.Build.emit1 (TermIR.Instr.Tag c) >>= widen

            value : PrimFn m -> Vect m Reg -> B (TermIR.Opnd v IRCommon.Ty.Val)
            value (Add DoubleType) [x, y] = doubleArith IRCommon.Op.FAdd x y
            value (Sub DoubleType) [x, y] = doubleArith IRCommon.Op.FSub x y
            value (Mul DoubleType) [x, y] = doubleArith IRCommon.Op.FMul x y
            value (Div DoubleType) [x, y] = doubleArith IRCommon.Op.FDiv x y
            value (Neg DoubleType) [x] = do
              a <- valDouble (get env x)
              f <- TermIR.Build.emit1 (TermIR.Instr.FNeg a)
              doubleVal f
            value DoubleSqrt [x] = do
              a <- valDouble (get env x)
              f <- TermIR.Build.emit1 (TermIR.Instr.FSqrt a)
              doubleVal f
            value DoubleFloor [x] = valDouble (get env x) >>= Doubles.roundWhole False >>= doubleVal
            value DoubleCeiling [x] =
              valDouble (get env x) >>= Doubles.roundWhole True >>= doubleVal
            value (LT DoubleType) [x, y] = doubleOrder IRCommon.Op.LtS x y
            value (LTE DoubleType) [x, y] = doubleOrder IRCommon.Op.LeS x y
            value (EQ DoubleType) [x, y] = doubleOrder IRCommon.Op.EqR x y
            value (GTE DoubleType) [x, y] = doubleOrder IRCommon.Op.GeS x y
            value (GT DoubleType) [x, y] = doubleOrder IRCommon.Op.GtS x y
            value (Add ty) [x, y] =
              withWidth ty "addition"
                (\w => arithmetic w Add Types.IntegerRoutine.Add (get env x) (get env y))
            value (Sub ty) [x, y] =
              withWidth ty "subtraction"
                (\w => arithmetic w Sub Types.IntegerRoutine.Sub (get env x) (get env y))
            value (Mul ty) [x, y] =
              withWidth ty "multiplication"
                (\w => arithmetic w Mul Types.IntegerRoutine.Mul (get env x) (get env y))
            value (Div ty) [x, y] =
              withWidth ty "division" (\w => division w False (get env x) (get env y))
            value (Mod ty) [x, y] =
              withWidth ty "remainder" (\w => division w True (get env x) (get env y))
            value (Neg ty) [x] = withWidth ty "negation" (\w => negation w (get env x))
            value (ShiftL ty) [x, y] =
              withWidth ty "a left shift" (\w => shifting w True (get env x) (get env y))
            value (ShiftR ty) [x, y] =
              withWidth ty "a right shift" (\w => shifting w False (get env x) (get env y))
            value (BAnd ty) [x, y] =
              withWidth ty "bitwise and"
                (\w =>
                 arithmetic w IRCommon.Op.And Types.IntegerRoutine.And (get env x) (get env y))
            value (BOr ty) [x, y] =
              withWidth ty "bitwise or"
                (\w => arithmetic w IRCommon.Op.Or Types.IntegerRoutine.Or (get env x) (get env y))
            value (BXOr ty) [x, y] =
              withWidth ty "bitwise xor"
                (\w =>
                 arithmetic w IRCommon.Op.Xor Types.IntegerRoutine.Xor (get env x) (get env y))
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
            value StrAppend [a, b] = do [r] <- strings Types.StringRoutine.Append
                                          [get env a, get env b]
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
            value (LT ty) [x, y] =
              withWidth ty "<" (\w => comparison w IRCommon.Op.LtS (get env x) (get env y))
            value (LTE ty) [x, y] =
              withWidth ty "<=" (\w => comparison w IRCommon.Op.LeS (get env x) (get env y))
            value (EQ ty) [x, y] =
              withWidth ty "==" (\w => comparison w IRCommon.Op.EqR (get env x) (get env y))
            value (GTE ty) [x, y] =
              withWidth ty ">=" (\w => comparison w IRCommon.Op.GeS (get env x) (get env y))
            value (GT ty) [x, y] =
              withWidth ty ">" (\w => comparison w IRCommon.Op.GtS (get env x) (get env y))
            value fn _ = TermIR.Build.unsupported ("the primitive " ++ show fn)

------------------------------------------------------------------------------
-- The program

||| What a declaration of the program is made from: what a function of the
||| program is lowered from, or a routine of the runtime declared outside
||| it (`Outside`).
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
  | ||| A foreign function the system tier implements, of the arity: a call
    ||| of the ordinary function that does, of the same type, and of the
    ||| arity it is written of.
    Implemented Nat Name Nat
  | ||| A top-level constant, evaluated on its first use and kept: its cell
    ||| in `Area.CONSTANTS`, and the function of no arguments that computes
    ||| its value.
    Constant Nat Name
  | ||| The entry, when the program has none.
    NoEntry
  | ||| A routine of the runtime that the lowering calls by its name, whose
    ||| form the program is not lowered with: declared outside the program,
    ||| of its port's registers, so that a call of it stops the rendering,
    ||| which names it.
    Outside

parameters {enc : Types.Enc} {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val}

  ||| A function that has a flat form, as the wrapper around the form's.
  lowerBoundary : (d : TermIR.Decls enc) -> Refs enc d -> LowerFlat.Callee d ->
                  List Flat.Exp.Shape -> Flat.Exp.Shape ->
                  (arity : Nat) ->
                  TermIR.Build.Closed d IRCommon.Conv.CPS False (replicate arity IRCommon.Ty.Val)
  lowerBoundary d refs ce ss r arity = TermIR.Build.build $ \ps =>
    boundary d refs ce ss r (allVals ps)

  ||| A function's definition, from its plan.
  planDef : (d : TermIR.Decls enc) -> Refs enc d -> LowerFlat.Forms enc d -> (s : TermIR.Sig enc) ->
            Plan ->
            TermIR.Def d s
  planDef d refs fs (TermIR.MkSig n IRCommon.Conv.CPS ps False) (FromVM args body) =
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
                      TermIR.Build.Closed d IRCommon.Conv.CPS False
                      (replicate (length args) IRCommon.Ty.Val)
      lowerFunction d refs args body = TermIR.Build.build $ \ps =>
        lower d refs (fromList (zip args (map (\x => (x, Nothing)) (allVals ps)))) True
          (annotate (singleton (-1)) body)
              (\env => TermIR.Build.return (get env RVal))
  planDef d refs fs (TermIR.MkSig n IRCommon.Conv.CPS ps False) (Boundary arity fd ss r) =
    case (decEq ps (replicate arity IRCommon.Ty.Val), lookup fd.name fs.callees) of
      (Yes Refl, Just ce) =>
        TermIR.Def.Defined
          (fromMaybe (TermIR.Body.Unsupported "a level outside its context")
           (TermIR.Build.close (lowerBoundary d refs ce ss r arity)))
      _ => TermIR.Def.Defined (TermIR.Body.Unsupported ("the boundary of " ++ show n))
  planDef d refs fs (TermIR.MkSig n (IRCommon.Conv.Direct rs False) ps cv) (Form fd) =
    case (decEq rs (LowerFlat.tys fd.result),
      decEq ps (LowerFlat.tys (LowerFlat.paramsLayout fd.params)),
        decEq cv (Linkage.ConvertsIn.convertsIn fd.name)) of
      (Yes Refl, Yes Refl, Yes Refl) =>
        TermIR.Def.Defined
          (fromMaybe (TermIR.Body.Unsupported "a level outside its context")
           (TermIR.Build.close (LowerFlat.lowerForm d fs fd)))
      _ =>
        TermIR.Def.Defined
          (TermIR.Body.Unsupported ("the registers of the flat form of " ++ show fd.name))
  planDef d refs fs (TermIR.MkSig n IRCommon.Conv.CPS ps False) (Foreign arity) =
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
        fromMaybe (TermIR.Build.unsupported ("the foreign function " ++ show n))
          (stringIterator d refs n (allVals ps))
  planDef d refs fs (TermIR.MkSig n IRCommon.Conv.CPS ps False) (Implemented arity impl m) =
    case (decEq ps (replicate arity IRCommon.Ty.Val), lookup impl refs.funs) of
      (Yes Refl, Just (TermIR.MkSig _ IRCommon.Conv.CPS ps' _ ** var)) =>
        case decEq ps' (replicate m IRCommon.Ty.Val) of
          Yes Refl =>
            if m > arity then unbound "of more parameters than" else
              TermIR.Def.Defined
                (fromMaybe (TermIR.Body.Unsupported "a level outside its context")
                 (TermIR.Build.close (TermIR.Build.build $ \args => bound var (allVals args))))
          No _ => unbound "of other parameters than"
      _ => unbound "missing for"
    where
      unbound : {0 s' : TermIR.Sig enc} -> String -> TermIR.Def d s'
      unbound why =
        TermIR.Def.Defined (TermIR.Body.Unsupported ("the implementation " ++ show impl ++ " "
                                                     ++ why ++ " " ++ show n))

      -- a function's value applied to the arguments, the last in tail position
      applied : TermIR.Opnd v' IRCommon.Ty.Val -> List (TermIR.Opnd v' IRCommon.Ty.Val) ->
                TermIR.Build.End d IRCommon.Conv.CPS False v' l'
      applied f [] = TermIR.Build.return f
      applied f [x] = TermIR.Build.tailApply f x
      applied f (x :: xs) = do
        f' <- TermIR.Build.apply f x
        applied f' xs

      -- the first `k` of the operands, and the rest
      splitVals : (k : Nat) -> List (TermIR.Opnd v' IRCommon.Ty.Val) ->
                  Maybe (All (TermIR.Opnd v') (replicate k IRCommon.Ty.Val),
                         List (TermIR.Opnd v' IRCommon.Ty.Val))
      splitVals Z xs = Just ([], xs)
      splitVals (S k) [] = Nothing
      splitVals (S k) (x :: xs) = map (\(fs, rs) => (x :: fs, rs)) (splitVals k xs)

      -- the implementation called with the arguments it takes, and what it
      -- gives applied to the rest: an implementation written of fewer
      -- arguments than its type has, as `toPrim` makes one, gives a function
      bound : {k : Nat} ->
              TermIR.Var d.sigs
              (TermIR.MkSig nm IRCommon.Conv.CPS (replicate k IRCommon.Ty.Val) cv) ->
              List (TermIR.Opnd v' IRCommon.Ty.Val) ->
              TermIR.Build.End d IRCommon.Conv.CPS False v' l'
      bound var args = case splitVals k args of
        Just (first, []) => TermIR.Build.tailCall var first
        Just (first, rest) => do
          f <- TermIR.Build.call var first
          applied f rest
        Nothing => TermIR.Build.unsupported ("the arguments of " ++ show impl)

  planDef d refs fs (TermIR.MkSig n IRCommon.Conv.CPS [] False) (Constant i body) =
    case lookup body refs.funs of
      Just (TermIR.MkSig _ IRCommon.Conv.CPS ps _ ** var) => case decEq ps [] of
        Yes Refl =>
          TermIR.Def.Defined
            (fromMaybe (TermIR.Body.Unsupported "a level outside its context")
             (TermIR.Build.close (lowerConstant var)))
        No _ => TermIR.Def.Defined (TermIR.Body.Unsupported ("the value of " ++ show n))
      _ => TermIR.Def.Defined (TermIR.Body.Unsupported ("the value of " ++ show n))
    where
      ||| The constant's cell: its first word 1 once the value, its second
      ||| word, is there. The value comes from the cell, or from the call of
      ||| the function that computes it, which the cell then keeps.
      lowerConstant : TermIR.Var d.sigs (TermIR.MkSig nm IRCommon.Conv.CPS [] cv) ->
                      TermIR.Build.Closed d IRCommon.Conv.CPS False []
      lowerConstant var = TermIR.Build.build $ \[] => do
        a <- TermIR.Build.emit1 (TermIR.Instr.AreaAddr Area.CONSTANTS)
        ready <- TermIR.Build.emit1 (TermIR.Instr.Load IRCommon.Ty.W64 (cell a 0))
        TermIR.Build.branch IRCommon.Op.EqR ready (TermIR.Opnd.W 1)
          (do v <- TermIR.Build.emit1 (TermIR.Instr.Load IRCommon.Ty.Val (cell a 8))
              TermIR.Build.return v)
          (do v <- TermIR.Build.call var []
              -- the area's address again, as no register outlives the call
              a' <- TermIR.Build.emit1 (TermIR.Instr.AreaAddr Area.CONSTANTS)
              TermIR.Build.emit0 (TermIR.Instr.Store IRCommon.Ty.Val (cell a' 8) v)
              TermIR.Build.emit0 (TermIR.Instr.Store IRCommon.Ty.W64 (cell a' 0) (TermIR.Opnd.W 1))
              TermIR.Build.return v)
        where
          at : (word : Int) -> Int
          at w = cast (Area.constantOffset (cast i)) + w

          cell : TermIR.Opnd v' IRCommon.Ty.ByteAddr -> (word : Int) ->
                 TermIR.Mem v' (TermIR.Mem.MkCell Nothing False (at word))
          cell a w = TermIR.MkMem (TermIR.Mem.AtBytes a) Nothing (at w)
  planDef d refs fs (TermIR.MkSig n (IRCommon.Conv.Direct rs False) ps False) Outside =
    TermIR.Def.External
  planDef d refs fs s NoEntry =
    TermIR.Def.Defined (TermIR.Body.Unsupported "a program without __mainExpression")
  planDef d refs fs s _ =
    TermIR.Def.Defined (TermIR.Body.Unsupported ("the definition of " ++ show s.name))

  defs : (d : TermIR.Decls enc) -> Refs enc d -> LowerFlat.Forms enc d ->
         (es : List (TermIR.Sig enc, Plan)) ->
         All (TermIR.Def d) (map Builtin.fst es)
  defs d refs fs [] = []
  defs d refs fs ((s, p) :: es) = planDef d refs fs s p :: defs d refs fs es

||| A static object's definition, made once the declarations are fixed,
||| from their statics by name: an object that holds another's address
||| finds that static among them, and one that names no static is an
||| error, which names the object.
0 DeferredStatic : Types.Enc -> TermIR.StaticSig -> Type
DeferredStatic enc s =
  (0 d : TermIR.Decls enc) -> SortedMap Name (s' ** TermIR.Var d.statics s') ->
  Either String (TermIR.StaticDef d s)

||| The program of the declarations, the entry first; or, of a static
||| object that holds the address of a static no declaration makes, an
||| error that names it.
program : {enc : Types.Enc} -> {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} ->
          List Flat.Exp.FlatDef ->
          Flat.Exp.Shapes -> Linkage.Realised -> (typeCons : SortedMap Name Int) ->
          (staticReads : SortedMap Name StaticRead) -> (constants : Nat) -> Plan ->
          (es : List (TermIR.Sig enc, Plan)) -> (rs : List (s ** DeferredStatic enc s)) ->
          Either String (TermIR.Program.TermProgram enc)
program forms shapes realised typeCons staticReads constants entry es rs =
  case choose
    (Data.Distinct.distinct (map (.name) (mainSig :: map Builtin.fst es))
     && Data.Distinct.distinct (map (.sym) (map DPair.fst rs))) of
    Left ok => do
      statics <- staticDefs (programDecls es rs) (staticVars (programDecls es rs)) rs
      Right
        (programDecls es rs ** TermIR.MkProgram
                     (defs (programDecls es rs) (declsRefs (programDecls es rs))
                       (LowerFlat.MkForms (LowerFlat.callees (programDecls es rs) forms) shapes
                         realised.services
                         realised.externs realised.primitives constants
                         (staticVars (programDecls es rs)) staticReads)
                           ((mainSig, entry) :: es))
                     statics (TermIR.Program.MkEntry TermIR.Var.here)
                       (IRCommon.MkConIds
                         [(n, cast i) | (n, i) <- Data.SortedMap.toList typeCons]))
    Right _ =>
      Right
        (TermIR.MkDecls [mainSig] [] ** TermIR.MkProgram
                     [TermIR.Def.Defined
                       (TermIR.Body.Unsupported "a program with two definitions of one name")]
                       []
                       (TermIR.Program.MkEntry TermIR.Var.here) IRCommon.ConIds.noConIds)
  where
    ||| Each static object of the declarations by name, with its variable.
    staticVars : (d : TermIR.Decls enc) -> SortedMap Name (s ** TermIR.Var d.statics s)
    staticVars d = fromList [(s.sym, (s ** v)) | (s ** v) <- TermIR.Var.enumerate d.statics]

    declsRefs : (d : TermIR.Decls enc) -> Refs enc d
    declsRefs d = MkRefs (fromList [(s.name, (s ** v)) | (s ** v) <- TermIR.Var.enumerate d.sigs])
                      (staticVars d) realised typeCons staticReads

    -- each static's definition, made from the declarations' statics by name
    staticDefs : (0 d : TermIR.Decls enc) -> SortedMap Name (s ** TermIR.Var d.statics s) ->
                 (rs : List (s ** DeferredStatic enc s)) ->
                 Either String (All (TermIR.StaticDef d) (map DPair.fst rs))
    staticDefs d stats [] = Right []
    staticDefs d stats ((_ ** def) :: rs) = do
      sd <- def d stats
      sds <- staticDefs d stats rs
      Right (sd :: sds)

    ||| The entry's signature: CPS, of no parameters.
    mainSig : TermIR.Sig enc'
    mainSig = TermIR.MkSig mainExpression IRCommon.Conv.CPS [] False

    ||| The declarations: the entry first, the other functions, the statics.
    programDecls : (es : List (TermIR.Sig enc, Plan)) -> (rs : List (s ** DeferredStatic enc s)) ->
                   TermIR.Decls enc
    programDecls es rs = TermIR.MkDecls (mainSig :: map Builtin.fst es) (map DPair.fst rs)

||| Whether a value of the C type is held as a flat value of the skeleton:
||| an integer as its machine type, a `Char`, a `Double`, the world, `()`, a
||| primitive's `IORes`, a `String` held as ordinary code holds it, a
||| pointer, `Ptr a` or `AnyPtr`, held as ordinary code holds it, an object
||| of its address, and a `Buffer` held as ordinary code holds it.
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
cfAgrees (CFIORes t) (Flat.Exp.SCon n [s]) = n == NS (mkNamespace "PrimIO") (UN (Basic "IORes"))
  && cfAgrees t s
cfAgrees CFString (Flat.Exp.SCon n [Flat.Exp.SPrim StringType]) = n == Flat.Exp.uniformType
cfAgrees CFPtr (Flat.Exp.SCon n [Flat.Exp.SCon p _]) =
  n == Flat.Exp.uniformType
  &&
    (p == NS (mkNamespace "PrimIO") (UN (Basic "Ptr")) || p
     == NS (mkNamespace "PrimIO") (UN (Basic "AnyPtr")))
cfAgrees CFBuffer (Flat.Exp.SCon n [Flat.Exp.SCon b _]) =
  n == Flat.Exp.uniformType && b == NS (mkNamespace "Data.Buffer") (UN (Basic "Buffer"))
cfAgrees (CFUser t _) (Flat.Exp.SCon n [Flat.Exp.SCon t' _]) = n == Flat.Exp.uniformType && t == t'
cfAgrees _ _ = False

------------------------------------------------------------------------------
-- The runtime's routines

||| The routines of the runtime that the lowering of the VMCode may call,
||| by the names generated code calls them by: the string and `Integer`
||| routines of its primitive operations (`op`), of its cases on strings
||| (`stringCase`) and of the functions of the string iterator
||| (`stringIterator`), as the loaded runtime realises the contract. Each
||| construct counts the routines its code calls, whatever the values, so
||| this is a superset of those the lowering calls: a cast it folds while
||| compiling counts too, and so does a function's body when the function
||| has a flat form, whose boundary is lowered instead. The program's reach
||| of the runtime is found from these (`Native.Codegen.ProgramReach`), so
||| a routine called that this misses is outside the program, and its call
||| stops the compile (`Outside`).
export
calledRoutines : Linkage.Realised -> List (Name, VMDef) -> SortedSet Name
calledRoutines realised = foldl definition empty
  where
    ||| A string routine, by the name the lowering calls it by (`strings`).
    string : Types.StringRoutine -> SortedSet Name -> SortedSet Name
    string c s = maybe s (\n => insert n s) (Linkage.Routine.stringRoutine realised c)

    ||| An `Integer` routine, by the name the lowering calls it by
    ||| (`integers`, `integerCall`).
    integer : Types.IntegerRoutine -> SortedSet Name -> SortedSet Name
    integer c s = maybe s (\n => insert n s) (Linkage.Routine.integerRoutine realised c)

    ||| An integer operation's `Integer` routine, which the lowering calls at
    ||| `Integer`'s width, unbounded, and at no other (`withWidth`).
    unbounded : PrimType -> Types.IntegerRoutine -> SortedSet Name -> SortedSet Name
    unbounded ty c s = case IntWidth.intWidth ty of
      Just IntWidth.Unbounded => integer c s
      _ => s

    ||| A comparison's routine: strings by the string routines' order
    ||| (`stringOrder`), an `Integer` by its own (`comparison`).
    order : PrimType -> SortedSet Name -> SortedSet Name
    order StringType = string Types.StringRoutine.Compare
    order ty = unbounded ty Types.IntegerRoutine.Compare

    ||| The routines a cast's code calls, by the cast's way (`CastWay`). The
    ||| `Integer` routines make an `Integer` beyond the fixnums a bounded
    ||| integer, and a 64-bit integer beyond them an `Integer` (`retype`);
    ||| an `Integer` a double and back; and one beyond the fixnums its
    ||| decimal text, and text an `Integer`. The string routines make a
    ||| character a string, a word its decimal text, text a word, and a
    ||| double its text and back.
    way : CastWay -> SortedSet Name -> SortedSet Name
    way (CastWay.Retype IntWidth.Unbounded (IntWidth.Bounded _ _)) =
      integer Types.IntegerRoutine.ToBits64
    way (CastWay.Retype (IntWidth.Bounded Width.Whole True) IntWidth.Unbounded) =
      integer Types.IntegerRoutine.FromInt64
    way (CastWay.Retype (IntWidth.Bounded Width.Whole False) IntWidth.Unbounded) =
      integer Types.IntegerRoutine.FromBits64
    way (CastWay.Retype _ _) = id
    way (CastWay.ToChar _) = id
    way (CastWay.IntToDouble IntWidth.Unbounded) = integer Types.IntegerRoutine.ToDouble
    way (CastWay.IntToDouble (IntWidth.Bounded _ _)) = id
    way (CastWay.DoubleToInt IntWidth.Unbounded) = integer Types.IntegerRoutine.FromDouble
    way (CastWay.DoubleToInt (IntWidth.Bounded _ _)) = id
    way CastWay.CharString = string Types.StringRoutine.Cons
    way (CastWay.Decimal IntWidth.Unbounded) =
      string Types.StringRoutine.ShowSigned . integer Types.IntegerRoutine.ToDecimal
    way (CastWay.Decimal (IntWidth.Bounded _ True)) = string Types.StringRoutine.ShowSigned
    way (CastWay.Decimal (IntWidth.Bounded _ False)) = string Types.StringRoutine.ShowUnsigned
    way (CastWay.ReadInteger IntWidth.Unbounded) = integer Types.IntegerRoutine.FromDecimal
    way (CastWay.ReadInteger (IntWidth.Bounded _ _)) = string Types.StringRoutine.ReadWord
    way CastWay.ShowDouble = string Types.StringRoutine.ShowDouble
    way CastWay.ReadDouble = string Types.StringRoutine.ReadDouble
    way CastWay.NoCast = id

    ||| The routines a primitive operation's code calls (`op`). Each
    ||| primitive is named, so that one Idris adds stops the build here.
    primitive : PrimFn n -> SortedSet Name -> SortedSet Name
    primitive (Add ty) = unbounded ty Types.IntegerRoutine.Add
    primitive (Sub ty) = unbounded ty Types.IntegerRoutine.Sub
    primitive (Mul ty) = unbounded ty Types.IntegerRoutine.Mul
    primitive (Div ty) = unbounded ty Types.IntegerRoutine.Div
    primitive (Mod ty) = unbounded ty Types.IntegerRoutine.Mod
    primitive (Neg ty) = unbounded ty Types.IntegerRoutine.Neg
    primitive (ShiftL ty) = unbounded ty Types.IntegerRoutine.Shl
    primitive (ShiftR ty) = unbounded ty Types.IntegerRoutine.Shr
    primitive (BAnd ty) = unbounded ty Types.IntegerRoutine.And
    primitive (BOr ty) = unbounded ty Types.IntegerRoutine.Or
    primitive (BXOr ty) = unbounded ty Types.IntegerRoutine.Xor
    primitive (LT ty) = order ty
    primitive (LTE ty) = order ty
    primitive (EQ ty) = order ty
    primitive (GTE ty) = order ty
    primitive (GT ty) = order ty
    primitive StrLength = string Types.StringRoutine.Length
    primitive StrHead = string Types.StringRoutine.Head
    primitive StrTail = string Types.StringRoutine.Tail
    primitive StrIndex = string Types.StringRoutine.Index
    primitive StrCons = string Types.StringRoutine.Cons
    primitive StrAppend = string Types.StringRoutine.Append
    primitive StrReverse = string Types.StringRoutine.Reverse
    primitive StrSubstr = string Types.StringRoutine.Substr
    primitive DoubleExp = id
    primitive DoubleLog = id
    primitive DoublePow = id
    primitive DoubleSin = id
    primitive DoubleCos = id
    primitive DoubleTan = id
    primitive DoubleASin = id
    primitive DoubleACos = id
    primitive DoubleATan = id
    primitive DoubleSqrt = id
    primitive DoubleFloor = id
    primitive DoubleCeiling = id
    primitive (Cast from to) = way (CastWay.castWay from to)
    primitive BelieveMe = id
    primitive Crash = id

    ||| Whether a case's constant is a string's, which the lowering compares
    ||| with the value by the string routines' order (`stringCase`).
    isText : Constant -> Bool
    isText (Str _) = True
    isText _ = False

    mutual
      ||| The routines the instructions' code calls.
      instructions : SortedSet Name -> List VMInst -> SortedSet Name
      instructions = foldl instruction

      ||| The routines an instruction's code calls, its alternatives' among
      ||| them. Each instruction is named, as each primitive is.
      instruction : SortedSet Name -> VMInst -> SortedSet Name
      instruction s (DECLARE _) = s
      instruction s START = s
      instruction s (ASSIGN _ _) = s
      instruction s (MKCON {}) = s
      instruction s (MKCLOSURE {}) = s
      instruction s (MKCONSTANT _ _) = s
      instruction s (APPLY {}) = s
      instruction s (CALL {}) = s
      instruction s (OP _ fn _) = primitive fn s
      instruction s (EXTPRIM {}) = s
      instruction s (CASE _ alts d) = alternatives (map snd alts) d s
      instruction s (CONSTCASE _ alts d) =
        alternatives (map snd alts) d
          (if any (isText . fst) alts then string Types.StringRoutine.Compare s else s)
      instruction s (PROJECT {}) = s
      instruction s (NULL _) = s
      instruction s (ERROR _) = s

      ||| The routines the alternatives' code and the default's call.
      alternatives : List (List VMInst) -> Maybe (List VMInst) -> SortedSet Name -> SortedSet Name
      alternatives alts d s = maybe id (flip instructions) d (foldl instructions s alts)

    ||| The routines a definition's code calls: a function's body's, and
    ||| those of a function of the string iterator. An error is not lowered.
    definition : SortedSet Name -> (Name, VMDef) -> SortedSet Name
    definition s (_, MkVMFun _ body) = instructions s body
    definition s (n, MkVMForeign {}) =
      if n == iterator "uncons"
        then string Types.StringRoutine.CharAt (string Types.StringRoutine.After s)
      else if n == iterator "withIteratorString" then string Types.StringRoutine.From s
      else s
    definition s (_, MkVMError _) = s

||| That every routine the runtime has, as the loaded runtime realises the
||| contract under the encoding, has a flat form of its port's registers
||| among the runtime's forms: what `checkRoutines` gives when they do.
||| Nothing else makes one, and `lowerProgram` takes one, so that no program
||| is lowered against a runtime whose routines were not checked.
export
data RoutinesChecked : Types.Enc -> Linkage.Realised -> Type where
  ||| The routines of the contract as realised, checked.
  MkRoutinesChecked : {0 enc : Types.Enc} -> {0 realised : Linkage.Realised} ->
                      RoutinesChecked enc realised

||| Check that every routine the runtime has, as the loaded runtime realises
||| the contract, has a flat form of the registers its port says: its
||| parameters' and its result's are those generated code calls it with.
||| The form of each is looked up by its name among the runtime's (`form`),
||| not among those a program is lowered with, so that a runtime that does
||| not meet the contract is refused at every compile, whichever routines
||| the program calls. The error names the routine, with the form's
||| registers and the port's where they differ.
export
checkRoutines : (enc : Types.Enc) -> (realised : Linkage.Realised) ->
                (form : Name -> Maybe Flat.Exp.FlatDef) ->
                Either String (RoutinesChecked enc realised)
checkRoutines enc realised form =
  MkRoutinesChecked <$ traverse_ provided (Linkage.Routine.routines {enc} realised)
  where
    ||| The routine's form, of its port's registers.
    provided : Linkage.Routine.RoutineCall enc -> Either String ()
    provided r =
      case form r.name of
        Nothing =>
          Left ("the runtime has no routine " ++ show r.name ++ ", which generated code calls")
        Just fd =>
          let rs = LowerFlat.tys {enc} fd.result
              ps = LowerFlat.tys {enc} (LowerFlat.paramsLayout fd.params)
          in if rs == r.results && ps == r.params then Right ()
             else Left ("the runtime's " ++ show r.name ++ " has the form "
                        ++ show ps ++ " -> " ++ show rs
                        ++ ", but its port is "
                        ++ show r.params ++ " -> " ++ show r.results)

------------------------------------------------------------------------------
-- A whole program

||| A whole program, as a term: every function and foreign function, the
||| runtime's routines, the statics of the nullary constructors, of the
||| big constants and of the constants marked static, and
||| `__mainExpression` as the entry, first.
|||
||| The flat forms given are those of the program's functions and of what
||| they call, with the shapes of the data types they handle. A function
||| that has a form becomes the boundary to it, if its arity is the form's
||| and the shapes of its parameters and result are known, and every form
||| becomes a `Direct` function.
|||
||| A foreign function the runtime implements by a flat function (`flat`,
||| as `Native.Codegen.Linkage.ForeignFunctions` finds them) becomes the
||| boundary to it, which must take and return, position by position, what
||| the foreign function's C types say; one that does not is an error. One
||| it implements by an ordinary function (`implemented`) becomes a call of
||| it.
|||
||| The runtime's routines, as the loaded runtime realises the contract
||| (`Native.Codegen.Linkage.Realised`), are called as the forms of their
||| names among those given, which must be the runtime's own, and those
||| forms are compiled with the program. The lowering checks no routine
||| itself: it takes the evidence (`RoutinesChecked`) that `checkRoutines`
||| found, among the runtime's forms, one of its port's registers for
||| each. The rendering and the seed reach some routines by their symbols
||| (`Linkage.Routine.RoutineCall.symbol`), which the rendering defines at
||| their forms, so the forms given must include those: one whose symbol
||| the image uses and whose form is not given is a label the link finds
||| missing. Each other routine, which the lowering calls by its name (a
||| string or `Integer` routine), is declared outside the program when
||| its form is not given, of its port's registers (`Outside`): a call of
||| one is left to the rendering, which refuses it with an error that
||| names the routine (`X86.Render.render`). A call of a routine whose
||| form is given but not as its port says, of other registers (which
||| `checkRoutines` refuses of the runtime's forms) or of a function that
||| may convert between words and addresses (`Linkage.ConvertsIn`), lowers
||| to a crash of the program, which names the routine. A call of one the
||| runtime does not have yet, of an encoding it has no module for, ends
||| the program as `Unsupported` does. The OS services' externs lower to
||| calls of the platform's functions for them, and the inline externs to
||| the instructions they stand for.
|||
||| Each constant the program marks static is given as code reads it
||| (`Native.Codegen.StaticRead`), and every read of it in VMCode is its
||| value, as is every read of it a flat form makes (`Flat.Exp.FStatic`);
||| the `constants`, those evaluated on their first use, are the others.
||| The static objects the reads name, and those they hold, are given by
||| name, each with what it holds (`staticObjects`), and are the program's.
||| The one each constant is read by must be laid out: one its header
||| cannot hold is an error, which names the constant. An object that holds
||| another holds its address, and one that holds an object not laid out is
||| an error, which names the holder. A flat form's read must be one flat
||| code holds (`LowerFlat.flatRead`): one it cannot is an error, which
||| names the form and the constant.
export
lowerProgram : (enc : Types.Enc) -> {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} -> Platform ->
               (realised : Linkage.Realised) -> (0 checked : RoutinesChecked enc realised) ->
               List Flat.Exp.FlatDef -> Flat.Exp.Shapes ->
               (staticReads : SortedMap Name StaticRead) ->
               (staticObjects : SortedMap Name ConstantWord.StaticPlan) ->
               (constants : List Name) -> (flat, implemented : List (Name, Name)) ->
               List (Name, VMDef) -> Either String (TermIR.Program.TermProgram enc)
lowerProgram enc platform realised _ forms shapes staticReads staticObjects constants flat
             implemented vmdefs0 = do
  let vmdefs = map (\(n, d) => (n, answered d)) vmdefs0
      -- the maps the helpers look in, made here once: a constant of the
      -- `where` block would be made again at each use
      byName = the (SortedMap Name Flat.Exp.FlatDef) (fromList [(fd.name, fd) | fd <- forms])
      cells = the (SortedMap Name Nat) (fromList (zip constants [0 .. length constants]))
  traverse_ (agrees byName) (mapMaybe boundForeign vmdefs)
  let entryPlan = case Data.List.lookup mainExpression vmdefs of
                    Just (MkVMFun [] body) => FromVM [] body
                    _ => NoEntry
      -- grown at its end: a list's `concatMap` would copy what it has so
      -- far at each function
      planned =
        foldl (\acc, sp => acc <>< kept cells sp) [<]
          (mapMaybe (plan byName) (filter ((/= mainExpression) . fst) vmdefs))
          <>> []
      others = planned
                 ++ [(LowerFlat.formSig fd, Form fd) | fd <- forms]
                 ++ outside (Data.SortedSet.fromList [fd.name | fd <- forms])
      -- the nullary constructors the boundaries may box, with constructor
      -- 0's, which a string iterator's end is
      boxing = fromList
        ((ConstantWord.nullaryCon 0, ConstantWord.Nullary 0)
           ::
             [(ConstantWord.nullaryCon c, ConstantWord.Nullary c)
              | c <- toList (concatMap (boxed . snd) planned)])
      -- each static once, in the order of their names, which is the order
      -- the image lays them out in: so the image is the same, byte for
      -- byte, whatever order the statics were collected in
      statics = Data.SortedMap.toList
                  (foldl mergeLeft boxing (staticObjects :: mapMaybe bodyStatics vmdefs))
      rs = mapMaybe ready statics
      laid = Data.SortedSet.fromList (map (\(s ** _) => s.sym) rs)
  -- the static object each constant marked static is read by, if it is
  -- read by one
  traverse_ (laidOut laid)
    (mapMaybe (\(n, rd) => (n,) <$> readObject rd) (Data.SortedMap.toList staticReads))
  traverse_ held [(fd.name, r) | fd <- forms, r <- Flat.Exp.formStatics fd]
  program forms shapes realised typeCons staticReads (length constants) entryPlan others rs
  where
    ||| A read of a constant marked static by the flat form of the name,
    ||| which flat code must hold as it is read at (`LowerFlat.flatRead`):
    ||| one it cannot is an error, which names the form and the constant.
    held : (Name, (Name, Flat.Exp.Skeleton, Flat.Exp.Layout)) -> Either String ()
    held (f, (n, sk, lay)) = case LowerFlat.flatRead enc.bignum staticReads n sk lay of
      Right _ => Right ()
      Left why => Left ("the flat form of " ++ show f ++ " reads " ++ why)

    ||| The static object a constant names as a value, if it names one
    ||| (`ConstantWord.constantWord`), and what it holds.
    constantObject : Constant -> Maybe (Name, ConstantWord.StaticPlan)
    constantObject k = either (const Nothing) snd (ConstantWord.constantWord enc.bignum k)

    ||| The static object a read of a constant marked static names, if it
    ||| names one: a literal's, as any literal's (`constantObject`), or its
    ||| own.
    readObject : StaticRead -> Maybe Name
    readObject (StaticRead.Literal k) = fst <$> constantObject k
    readObject StaticRead.Erased = Nothing
    readObject (StaticRead.Object o) = Just o

    ||| A constant marked static, with the static object it is read by,
    ||| which must be among those laid out: one that is not is an error.
    laidOut : SortedSet Name -> (Name, Name) -> Either String ()
    laidOut laid (n, o) =
      if contains o laid then Right ()
        else Left ("the constant " ++ show n ++ ", marked static, has a value whose static "
                   ++ "object its header cannot hold")

    -- `System.Info`'s externs, which every program of the platform answers
    -- alike, made the constants they are: the operating system's name and
    -- the code generator's.
    answered : VMDef -> VMDef
    answered (MkVMFun args body) = MkVMFun args (map inst body)
      where
        inst : VMInst -> VMInst
        inst i@(EXTPRIM r p []) =
          if p == NS (mkNamespace "System.Info") (UN (Basic "prim__os"))
            then MKCONSTANT r (Str (Platform.osName platform.os))
          else if p == NS (mkNamespace "System.Info") (UN (Basic "prim__codegen"))
            then MKCONSTANT r (Str "native")
          else i
        inst (CASE r alts dflt) =
          CASE r (map (\(t, is) => (t, map inst is)) alts) (map (map inst) dflt)
        inst (CONSTCASE r alts dflt) =
          CONSTCASE r (map (\(c, is) => (c, map inst is)) alts) (map (map inst) dflt)
        inst i = i
    answered d = d

    -- The type constructors the program builds or matches as values, each
    -- numbered by its place in the order of their names.
    typeCons : SortedMap Name Int
    typeCons = let ns = Prelude.toList (foldl defNames empty vmdefs0)
               in fromList (zip ns (map cast [0 .. length ns]))
      where
        mutual
          names : SortedSet Name -> List VMInst -> SortedSet Name
          names = foldl inst

          inst : SortedSet Name -> VMInst -> SortedSet Name
          inst s (MKCON _ (Right n) _) = Data.SortedSet.insert n s
          -- lint: allow trust-escape: VMCode nests its instruction lists in tuples, which
          -- totality checking does not see through
          inst s (CASE _ alts d) =
            assert_total
              (maybe id (flip names) d
                (foldl (\a, (t, is) => names (either (const a) (flip Data.SortedSet.insert a) t) is)
                   s alts))
          -- lint: allow trust-escape: as a case's
          inst s (CONSTCASE _ alts d) =
            assert_total (maybe id (flip names) d (foldl (\a, alt => names a (snd alt)) s alts))
          inst s _ = s

        defNames : SortedSet Name -> (Name, VMDef) -> SortedSet Name
        defNames s (_, MkVMFun _ body) = names s body
        defNames s _ = s

    ||| The routines of the runtime that the lowering calls by their names,
    ||| those reached by no symbol, whose forms are not given (`given` holds
    ||| the names of those that are), each declared outside the program by
    ||| the signature generated code calls it by (`routine`): its form's
    ||| name, `Direct`, of its port's registers, converting nothing. One
    ||| reached by its symbol is not declared: no call names it, and its
    ||| symbol is defined at its form.
    outside : (given : SortedSet Name) -> List (TermIR.Sig enc, Plan)
    outside given =
      [ (TermIR.MkSig (Linkage.Routine.flatName r.name) (IRCommon.Conv.Direct r.results False)
           r.params False, Outside)
      | r <- Linkage.Routine.routines {enc} realised, isNothing r.symbol
      , not (contains r.name given) ]

    boundForeign : (Name, VMDef) -> Maybe (Name, List CFType, CFType)
    boundForeign (n, MkVMForeign _ fargs ret) =
      if elem n (map fst flat)
      then Just (n, fargs, ret) else Nothing
    boundForeign _ = Nothing

    -- A foreign function and its implementation, position by position.
    agrees : (byName : SortedMap Name Flat.Exp.FlatDef) -> (Name, List CFType, CFType) ->
             Either String ()
    agrees byName (n, fargs, ret) = case Data.List.lookup n flat
      >>= \f =>
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
    boundaryPlan : (byName : SortedMap Name Flat.Exp.FlatDef) -> Name -> Nat -> Maybe Plan
    boundaryPlan byName n arity = do
      fd <- lookup n byName
        <|>
          (Data.List.lookup n flat >>= \f =>
           lookup f byName)
      guard (length fd.params == arity)
      ss <- traverse (Flat.Exp.skeletonShape shapes . skeleton) fd.params
      r <- Flat.Exp.skeletonShape shapes fd.resultSkeleton
      guard
        (map Flat.Exp.shapeLayout ss == map layout fd.params && Flat.Exp.shapeLayout r == fd.result)
      pure (Boundary arity fd ss r)

    ||| The ids of the constructors of no fields that ordinary code represents
    ||| as objects, in a shape: the statics boxing a value of it may need.
    nullaries : Flat.Exp.Shape -> Data.Builder Int
    nullaries (Flat.Exp.PrimShape _) = neutral
    nullaries Flat.Exp.UniformShape = neutral
    nullaries Flat.Exp.ByteAddrShape = neutral
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

    -- the parameters of a function of the program, as Idris compiled it
    functionArity : Name -> Nat
    functionArity f = case Data.List.lookup f vmdefs0 of
      Just (MkVMFun args _) => length args
      _ => 0

    plan : (byName : SortedMap Name Flat.Exp.FlatDef) -> (Name, VMDef) ->
           Maybe (TermIR.Sig enc, Plan)
    plan byName (n, MkVMFun args body) =
      Just (TermIR.MkSig n IRCommon.Conv.CPS (replicate (length args) IRCommon.Ty.Val) False,
            fromMaybe (FromVM args body) (boundaryPlan byName n (length args)))
    plan byName (n, MkVMForeign _ fargs _) =
      Just (TermIR.MkSig n IRCommon.Conv.CPS (replicate (length fargs) IRCommon.Ty.Val) False,
            maybe (fromMaybe (Foreign (length fargs)) (boundaryPlan byName n (length fargs)))
              (\impl => Implemented (length fargs) impl (functionArity impl))
              (Data.List.lookup n implemented))
    plan _ (n, MkVMError _) = Nothing

    -- a constant's plan as its cell's, and the function of its value
    kept : (cells : SortedMap Name Nat) -> (TermIR.Sig enc, Plan) -> List (TermIR.Sig enc, Plan)
    kept cells (s, p@(FromVM [] body)) = case lookup s.name cells of
      Just i =>
        [ (s, Constant i (constantValue s.name))
        , ({ name := constantValue s.name } s, p) ]
      Nothing => [(s, p)]
    kept _ sp = [sp]

    ||| The constants a function's locals may hold, and the static objects its
    ||| constants need, the empty string's among them whether the body names
    ||| it or not: the lowering makes a character's string from it (`Cons`
    ||| onto it), and an image leaves out a static nothing reaches. A cast of a
    ||| local holding a constant is folded while compiling, so every constant
    ||| a local may hold is followed through casts; the result may name
    ||| statics the lowering does not use, which costs only their bytes.
    instructionStatics : List VMInst -> SortedMap Name ConstantWord.StaticPlan
    instructionStatics body = snd (go body (empty, note (Str "") empty))
      where
        note : Constant -> SortedMap Name ConstantWord.StaticPlan ->
               SortedMap Name ConstantWord.StaticPlan
        note k ss = case constantObject k of
          Just (n, p) => insert n p ss
          Nothing => ss

        add : Int -> Constant ->
              (SortedMap Int (List Constant), SortedMap Name ConstantWord.StaticPlan) ->
              (SortedMap Int (List Constant), SortedMap Name ConstantWord.StaticPlan)
        add i k (known, ss) = (insert i (k :: fromMaybe [] (lookup i known)) known, note k ss)

        mutual
          go : List VMInst ->
               (SortedMap Int (List Constant), SortedMap Name ConstantWord.StaticPlan) ->
               (SortedMap Int (List Constant), SortedMap Name ConstantWord.StaticPlan)
          go [] acc = acc
          go (i :: is) acc = go is (one i acc)

          one : VMInst -> (SortedMap Int (List Constant), SortedMap Name ConstantWord.StaticPlan) ->
                (SortedMap Int (List Constant), SortedMap Name ConstantWord.StaticPlan)
          one (MKCONSTANT r k) acc@(known, ss) = case key r of
            Just i => add i k acc
            Nothing => (known, note k ss)
          -- a read of a constant marked static as a literal holds the
          -- literal, as a `MKCONSTANT` does (`lower`)
          one (CALL r _ f []) acc = case lookup f staticReads of
            Just (StaticRead.Literal k) => one (MKCONSTANT r k) acc
            _ => acc
          one (MKCON _ (Left c) []) (known, ss) =
            (known, insert (ConstantWord.nullaryCon c) (ConstantWord.Nullary c) ss)
          one (MKCON _ (Right n) []) (known, ss) = case lookup n typeCons of
            Just c => (known, insert (ConstantWord.nullaryCon c) (ConstantWord.Nullary c) ss)
            Nothing => (known, ss)
          one (OP r (Cast _ to) [x]) acc@(known, ss) =
            let folded = mapMaybe (\k => ConstantWord.intConst k >>= (castConstant to . snd))
                                  (fromMaybe [] (key x >>= \i => lookup i known))
            in case key r of
                 Just i => foldl (\a, f => add i f a) acc folded
                 Nothing => (known, foldl (flip note) ss folded)
          -- lint: allow trust-escape: VMCode nests its instruction lists in tuples, which totality
          -- checking does not see through
          one (CASE _ alts d) acc =
            assert_total (maybe id go d (foldl (\a, alt => go (snd alt) a) acc alts))
          -- a constant case compares with each alternative's constant, so a string
          -- among them needs its static as any constant does
          one (CONSTCASE _ alts d) acc =
            assert_total
              (maybe id go d
               (foldl (\(known, ss), alt => go (snd alt) (known, note (fst alt) ss)) acc alts))
          one _ acc = acc

    bodyStatics : (Name, VMDef) -> Maybe (SortedMap Name ConstantWord.StaticPlan)
    bodyStatics (_, MkVMFun _ body) = Just (instructionStatics body)
    bodyStatics _ = Nothing

    ||| A static object whose words name no other static: its definition, the
    ||| same whatever the declarations.
    standalone : ({0 d : TermIR.Decls enc'} -> TermIR.StaticDef d s) -> DeferredStatic enc' s
    standalone def = \_, _ => Right def

    ||| A static object of the program, its signature and its definition,
    ||| made once the declarations are fixed (`DeferredStatic`), if its
    ||| header can hold what it holds; one it cannot is left out, and a read
    ||| of it is the abort stub, which for a constant marked static is an
    ||| error (`laidOut`), as is an object that holds it.
    ready : (Name, ConstantWord.StaticPlan) -> Maybe (s ** DeferredStatic enc s)
    ready (n, ConstantWord.Nullary c) =
      case choose (TermIR.FieldTys.wellFormed (Types.Header.ConH {enc} (cast c) 0)) of
      Left ok =>
        Just
          (TermIR.MkStaticSig n Types.Kind.CON ** standalone (TermIR.MkStaticDef
           (Types.Header.ConH (cast c) 0) []))
      Right _ => Nothing
    ready (n, ConstantWord.Boxed p) =
      Just
        (TermIR.MkStaticSig n Types.Kind.INT64 ** standalone (TermIR.MkStaticDef Types.Header.Int64H
         [TermIR.StaticDef.SWord (cast p)]))
    ready (n, ConstantWord.BoxedDouble b) =
      Just
        (TermIR.MkStaticSig n Types.Kind.DOUBLE ** standalone (TermIR.MkStaticDef
         Types.Header.DoubleH [TermIR.StaticDef.SWord (cast b)]))
    ready (n, ConstantWord.Big v) = bigStatic enc (Types.BignumEnc.magnitudeWords (abs v))
      where
        ||| A big constant's static, a header of its sign and words, if the
        ||| encoding has a header for it and the header can hold it, matched on
        ||| the encoding so that the header's parts are of its type. Its words
        ||| name nothing, so it is defined for any declarations.
        bigStatic : (e : Types.Enc) -> (ws : List Int64) -> Maybe (s ** DeferredStatic e s)
        bigStatic e@(Types.MkEnc _ (Types.MkBignumEnc _ Types.BignumEnc.SignMagnitude) _) ws =
          let h =
                Types.Header.BignumH {enc = e}
                  (Types.BignumEnc.MkSignMagnitudeParts (v < 0) (length ws)) in
          case choose (TermIR.FieldTys.wellFormed h) of
            Left ok => do
              ws' <- toVect _ ws
              Just
                (TermIR.MkStaticSig n Types.Kind.BIGNUM ** standalone (TermIR.MkStaticDef h
                 (TermIR.StaticDef.wordFields (Types.Header.counts h) ws')))
            Right _ => Nothing
        bigStatic _ _ = Nothing
    ready (n, ConstantWord.Text s) = do
      (h ** ws) <- Strings.literal enc s
      case choose (TermIR.FieldTys.wellFormed h) of
        Left ok =>
          Just
            (TermIR.MkStaticSig n Types.Kind.STRING ** standalone (TermIR.MkStaticDef h
             (TermIR.StaticDef.wordFields (Types.Header.counts h) ws)))
        Right _ => Nothing
    -- a maker's object: its words after a header of their bytes, each
    -- word's pattern as is
    ready (n, ConstantWord.Words ws) =
      let h = Types.Header.BytesH {enc} (8 * length ws) in
      case choose (TermIR.FieldTys.wellFormed h) of
        Left ok => do
          ws' <- toVect _ (map (cast {to = Int64}) ws)
          Just
            (TermIR.MkStaticSig n Types.Kind.BYTES ** standalone (TermIR.MkStaticDef h
             (TermIR.StaticDef.wordFields (Types.Header.counts h) ws')))
        Right _ => Nothing
    -- a constructor with fields: its fields' words after a header of its id
    -- and their count, each a uniform value, a fixnum or the erased value as
    -- the value encoding has it, and another object as its address
    ready (n, ConstantWord.Constructor c ws) =
      case choose (TermIR.FieldTys.wellFormed (Types.Header.ConH {enc} (cast c) (length ws))) of
        Left ok =>
          Just
            (TermIR.MkStaticSig n Types.Kind.CON ** \_, stats =>
             map (\fs => TermIR.MkStaticDef (Types.Header.ConH (cast c) (length ws)) fs)
               (values stats ws))
        Right _ => Nothing
      where
        -- a word as a field that holds a uniform value: a fixnum as
        -- itself and the erased value as the fixnum 0, which the rendering
        -- encodes; another object as its address, found among the
        -- declarations' statics, or, if none is, an error that names this
        -- one
        value : {0 d : TermIR.Decls enc} -> SortedMap Name (s ** TermIR.Var d.statics s) ->
                ConstantWord.StaticWord -> Either String (TermIR.StaticDef.SField d IRCommon.Ty.Val)
        value stats (ConstantWord.Fixnum i {ok = inRange}) =
          Right (TermIR.StaticDef.SVal i {ok = inRange})
        value stats ConstantWord.Erased = Right (TermIR.StaticDef.SVal 0)
        value stats (ConstantWord.Object o) = case lookup o stats of
          Just (_ ** var) => Right (TermIR.StaticDef.SRef var)
          Nothing =>
            Left ("the static object " ++ show n ++ " holds the address of " ++ show o
                  ++ ", which no declaration makes")

        -- the words as the fields, in order, or the first error
        values : {0 d : TermIR.Decls enc} -> SortedMap Name (s ** TermIR.Var d.statics s) ->
                 (ws' : List ConstantWord.StaticWord) ->
                 Either String
                   (All (TermIR.StaticDef.SField d) (replicate (length ws') IRCommon.Ty.Val))
        values stats [] = Right []
        values stats (w :: rest) = do
          f <- value stats w
          fs <- values stats rest
          Right (f :: fs)
