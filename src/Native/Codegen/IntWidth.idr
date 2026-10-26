||| How the lowering holds an integer type, and wraps it (`IntWidth`): the
||| width each of its integer operations works at, and the one an integer
||| constant is read by (`Native.Codegen.ConstantWord.intConst`).
module Native.Codegen.IntWidth

import Core.TT.Primitive
import Native.Flat.Exp
import Native.Mach
import Native.Width

%default total

||| How an integer type is held, and how it wraps: of a machine type's width
||| and sign (`Mach.width`), or `Integer`'s, which only ordinary code has. A
||| narrow integer is always a fixnum; a 64-bit one is a fixnum or an `INT64`
||| box, by its pattern; an `Integer` a fixnum or a `BIGNUM`.
public export
data IntWidth = Bounded Width Bool | Unbounded

||| The width of an integer type. A `Char` counts as an unsigned narrow
||| integer, its code point, except as the target of a cast, which the
||| lowering (`Native.Codegen.Lower`) makes by its own rule: the value if it
||| is a Unicode scalar value, and 0 if not.
export
intWidth : PrimType -> Maybe IntWidth
intWidth IntegerType = Just Unbounded
intWidth t = (\(w, s) => Bounded w s) <$> (Flat.Exp.primMach t >>= Mach.width)
