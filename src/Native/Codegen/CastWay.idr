||| How the lowering of VMCode makes a cast between two primitive types
||| (`CastWay`), decided by the two types alone: the way says which code
||| makes the cast, and so which of the runtime's routines it may call,
||| whatever the value. The lowering (`Native.Codegen.Lower`) makes each
||| way's code; a cast of a known integer constant to an integer type or
||| to `Char` it folds while compiling instead. A flat form's casts, of
||| words alone, are its own lowering's (`Native.Codegen.LowerFlat`).
module Native.Codegen.CastWay

import Native.Codegen.IntWidth

import Core.TT.Primitive

%default total

||| How a cast is made, by its two types (`castWay`), each way shown as an
||| Idris program writes a cast of it. The widths are the types' as the
||| lowering holds them (`IntWidth`): the source's `wf` and the target's
||| `wt`.
public export
data CastWay : Type where
  ||| An integer as an integer type, wrapped to the target's width as
  ||| Idris's casts wrap: `cast {to = Bits8} (n : Int)`, or `ord c`, a
  ||| character's code point.
  Retype : (wf, wt : IntWidth) -> CastWay
  ||| An integer as a character, `chr n`: the value if it is a Unicode
  ||| scalar value, and `'\0'` if not.
  ToChar : (wf : IntWidth) -> CastWay
  ||| An integer as the nearest double, ties to even:
  ||| `cast {to = Double} (n : Int)`.
  IntToDouble : (wf : IntWidth) -> CastWay
  ||| A double as an integer type: its truncation toward zero, wrapped to
  ||| the type's width, and 0 if it is not finite:
  ||| `cast {to = Int} (d : Double)`.
  DoubleToInt : (wt : IntWidth) -> CastWay
  ||| A character as the string of it, `cast {to = String} c`.
  CharString : CastWay
  ||| An integer as its decimal text: `cast {to = String} (n : Int)`,
  ||| which `show n` is.
  Decimal : (wf : IntWidth) -> CastWay
  ||| A string as the integer it reads as, wrapped to the width as a cast
  ||| from `Integer` is, and 0 if it reads as none:
  ||| `cast {to = Int} (s : String)`.
  ReadInteger : (wt : IntWidth) -> CastWay
  ||| A double as its shortest decimal text:
  ||| `cast {to = String} (d : Double)`, which `show d` is.
  ShowDouble : CastWay
  ||| A string as the double it reads as, `cast {to = Double} (s : String)`.
  ReadDouble : CastWay
  ||| Any other pair of types: those Idris defines no cast between, such as
  ||| a string or a double as a character, and a character as a double.
  NoCast : CastWay

||| The way a cast from the first type to the second is made, by the two
||| types' widths (`IntWidth.intWidth`): an integer type and a character
||| have one; a string, a double and the world have none.
export
castWay : PrimType -> PrimType -> CastWay
castWay from to = case (IntWidth.intWidth from, IntWidth.intWidth to) of
  (Just wf, Just wt) => case to of
    CharType => ToChar wf
    _ => Retype wf wt
  (Just wf, Nothing) => case (from, to) of
    (CharType, StringType) => CharString
    (CharType, _) => NoCast
    (_, DoubleType) => IntToDouble wf
    (_, StringType) => Decimal wf
    _ => NoCast
  (Nothing, Just wt) => case (from, to) of
    (_, CharType) => NoCast
    (DoubleType, _) => DoubleToInt wt
    (StringType, _) => ReadInteger wt
    _ => NoCast
  (Nothing, Nothing) => case (from, to) of
    (DoubleType, StringType) => ShowDouble
    (StringType, DoubleType) => ReadDouble
    _ => NoCast
