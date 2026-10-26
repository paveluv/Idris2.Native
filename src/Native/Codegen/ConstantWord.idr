||| What a constant is as a uniform value of ordinary code (`constantWord`),
||| and what the static objects that hold such values hold (`StaticPlan`):
||| the one rule the lowering (`Native.Codegen.Lower`) reads each constant
||| by and collects the static objects of a program's constants by, so that
||| the two agree. A static object is named after what it holds, so that
||| every use of one value shares one object: a nullary constructor's by its
||| id, a 64-bit integer's outside the fixnum range by its pattern's signed
||| value, an `Integer`'s by its value, a double's by its bits, a string's
||| by its text. An integer constant is read by its type's width
||| (`Native.Codegen.IntWidth`), which the lowering's integer operations
||| wrap to as well.
module Native.Codegen.ConstantWord

import Native.Codegen.IntWidth

import Core.Name
import Core.Name.Namespace
import Core.TT.Primitive
import Data.So
import Native.Flat.ConstType
import Native.HeapObj.ValEnc
import Native.Primitive.DoubleBits
import Native.Types.BignumEnc as Types
import Native.Width

%default total

||| An integer constant: its type's width and its value.
export
intConst : Constant -> Maybe (IntWidth, Integer)
intConst k = [| (,) (Flat.ConstType.constType k >>= IntWidth.intWidth) (value k) |]
  where
    value : Constant -> Maybe Integer
    value (I n) = Just (cast n)
    value (I8 n) = Just (cast n)
    value (I16 n) = Just (cast n)
    value (I32 n) = Just (cast n)
    value (I64 n) = Just (cast n)
    value (BI n) = Just n
    value (B8 n) = Just (cast n)
    value (B16 n) = Just (cast n)
    value (B32 n) = Just (cast n)
    value (B64 n) = Just (cast n)
    value (Ch c) = Just (cast (ord c))
    value _ = Nothing

||| The signed value of a 64-bit pattern, from its value read signed or not.
export
patternValue : Integer -> Integer
patternValue v = if v >= 9223372036854775808 then v - 18446744073709551616 else v

||| The static object for every nullary constructor with this constructor id.
export
nullaryCon : Int -> Name
nullaryCon conId = NS (mkNamespace "_native") (UN (Basic ("con" ++ show conId)))

||| What a static object of the program holds.
public export
data StaticPlan
  = ||| Every nullary constructor with this id.
    Nullary Int
  | ||| A 64-bit pattern outside the fixnum range, by its signed value.
    Boxed Integer
  | ||| A double, by its bits.
    BoxedDouble Bits64
  | ||| An `Integer` outside the fixnum range, and its magnitude's words.
    Big Integer
  | ||| A string literal.
    Text String

||| A uniform value as a word of the program before the rendering encodes
||| it: a fixnum, the erased value, or the address of a static object.
public export
data StaticWord : Type where
  ||| A fixnum, its range decided when the word is made (`fixnumWord`).
  Fixnum : (i : Int64) -> {auto 0 ok : So (HeapObj.ValEnc.inFixnumRange (cast i))} -> StaticWord
  ||| The erased value.
  Erased : StaticWord
  ||| The address of the static object of this name.
  Object : Name -> StaticWord

||| An integer as a fixnum, if it is in the fixnum range: the test a
||| constant's word is made by, and the lowering's for an integer it is
||| given while compiling, such as a constructor's tag, so that the two
||| agree on the range.
export
fixnumWord : Integer -> Maybe StaticWord
fixnumWord v = let w : Int64 = cast v in
  if cast w /= v then Nothing else case choose (HeapObj.ValEnc.inFixnumRange (cast w)) of
    Left ok => Just (Fixnum w)
    Right _ => Nothing

||| What a constant is as a uniform value: its word, and the static object
||| the word names, if it names one, with what that object holds, which the
||| program's statics must have for the word to be read. It is the one rule
||| the lowering reads constants by and collects their static objects by.
||| An integer in the fixnum range is a fixnum, a 64-bit one by its
||| pattern's signed value. Outside the range a 64-bit integer is an `INT64`
||| box, and an `Integer` a `BIGNUM`, which only a bignum encoding with a
||| header for one lays out: under any other such a constant is no value,
||| and the error says so. A string and a double are objects, one per
||| literal and per double; the world and a type are the erased value.
export
constantWord : Types.BignumEnc -> Constant -> Either String (StaticWord, Maybe (Name, StaticPlan))
constantWord bignum k = case k of
  WorldVal => immediate Erased
  PrT _ => immediate Erased
  Str s => named (stringStatic s) (Text s)
  Db x => named (doubleStatic x) (BoxedDouble (Primitive.DoubleBits.doubleBits x))
  _ => case intConst k of
    Just (IntWidth.Bounded Width.Whole _, v) =>
      let p = patternValue v in maybe (named (int64Static p) (Boxed p)) immediate (fixnumWord p)
    Just (IntWidth.Unbounded, v) =>
      maybe (if Types.BignumEnc.headed bignum
               then named (bignumStatic v) (Big v)
               else
                 Left ("an Integer constant outside the fixnum range, under bignums in two's " ++
                       "complement"))
            immediate (fixnumWord v)
    Just (IntWidth.Bounded (Width.Narrow _) _, v) =>
      maybe (Left ("the constant " ++ show k)) immediate (fixnumWord v)
    Nothing => Left ("the constant " ++ show k)
  where
    -- the word of the static object of the name, which holds what the plan
    -- says
    named : Name -> StaticPlan -> Either String (StaticWord, Maybe (Name, StaticPlan))
    named n p = Right (Object n, Just (n, p))

    -- a word that is its own value, naming no static object
    immediate : StaticWord -> Either String (StaticWord, Maybe (Name, StaticPlan))
    immediate w = Right (w, Nothing)

    ||| The static object of a 64-bit integer constant outside the fixnum range,
    ||| by the signed value of its pattern.
    int64Static : Integer -> Name
    int64Static p = NS (mkNamespace "_native") (UN (Basic ("int64_" ++ show p)))

    ||| The static object of a double constant, by its bits: one per distinct
    ||| double, -0.0 apart from 0.0.
    doubleStatic : Double -> Name
    doubleStatic x =
      NS (mkNamespace "_native")
        (UN (Basic ("double_" ++ show (Primitive.DoubleBits.doubleBits x))))

    ||| The static object of an `Integer` constant outside the fixnum range.
    bignumStatic : Integer -> Name
    bignumStatic v = NS (mkNamespace "_native") (UN (Basic ("integer_" ++ show v)))

    ||| The static object of a string literal: one per distinct literal.
    stringStatic : String -> Name
    stringStatic s = NS (mkNamespace "_native") (UN (Basic ("string_" ++ show s)))
