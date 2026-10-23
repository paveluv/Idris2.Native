||| The primitive types Idris holds in one register (`Mach`, for machine
||| type), as a code of the contract's own, with the one table of each:
||| how a register holds it (`rep`), the Idris type it is (`type`), and its
||| width and sign (`width`).
|||
||| The codes are named as modern languages name their machine types: `I8`
||| to `I64` for the signed integers, `U8` to `U64` for `Bits8` to `Bits64`,
||| `F64` for `Double`; two Idris primitives that are types of their own
||| beside those: `IWord` for `Int`, which Idris keeps apart from `Int64`
||| though both are 64 bits, and `Rune` for `Char`, its code point in 32
||| bits, since Idris's parser takes `Int` and `Char` for its primitive
||| types wherever they are written, a constructor's name too; and `Bool`
||| for `Bool`, which flat code holds as its tag, 0 or 1, as it holds any
||| enumeration (`Flat.Exp.Ordinary`), so that a service's success is the
||| type it is. `Integer` and `String` are not machine types, being boxed,
||| and `%World` is erased. Every other module writes the codes qualified
||| (`Mach.I64`, `Mach.Bool`), so that they never meet Idris's own types of
||| the same names.
|||
||| An address is no machine type: it is no Idris primitive, has neither a
||| width nor a sign, and none of the primitives' operations apply to it.
||| Its rep is `Rep`'s own.
|||
||| Part of the contract between compiled code and the runtime, with the
||| heap-object model (`HeapObj.Shape` says what it is).
module Native.Mach

import Native.Rep
import Native.Width

%default total

||| A primitive type held in one register.
public export
data Mach = I8 | I16 | I32 | I64 | IWord | U8 | U16 | U32 | U64 | Rune | Bool | F64

||| How a register holds a value of the type: a double in a double's, every
||| integer, character and truth value in a word.
public export
rep : Mach -> Rep
rep F64 = Rep.Dbl
rep _ = Rep.Word

||| The Idris type the code is of.
public export
type : Mach -> Type
type I8 = Int8
type I16 = Int16
type I32 = Int32
type I64 = Int64
type IWord = Int
type U8 = Bits8
type U16 = Bits16
type U32 = Bits32
type U64 = Bits64
type Rune = Char
type Bool = Prelude.Bool
type F64 = Double

||| The width of an integer, a character or a truth value, and whether it is
||| signed: held in a word, extended from its width as it is signed or not.
||| A character is its code point, unsigned in 32 bits; a truth value 0 or
||| 1, a byte where it is stored; a double has none.
public export
width : Mach -> Maybe (Width, Prelude.Bool)
width I8 = Just (Width.Narrow Width.Sub8, True)
width I16 = Just (Width.Narrow Width.Sub16, True)
width I32 = Just (Width.Narrow Width.Sub32, True)
width I64 = Just (Width.Whole, True)
width IWord = Just (Width.Whole, True)
width U8 = Just (Width.Narrow Width.Sub8, False)
width U16 = Just (Width.Narrow Width.Sub16, False)
width U32 = Just (Width.Narrow Width.Sub32, False)
width U64 = Just (Width.Whole, False)
width Rune = Just (Width.Narrow Width.Sub32, False)
width Bool = Just (Width.Narrow Width.Sub8, False)
width F64 = Nothing
