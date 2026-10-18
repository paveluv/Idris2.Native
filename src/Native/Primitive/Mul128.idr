||| The 128-bit product of two words (`mul128`), a primitive
||| (`Native.Primitive` says what one is).
module Native.Primitive.Mul128

-- lint: allow public-import: the primitive's type, written by its signature,
-- reduces only where the signature and its reading are visible, so they are
-- wherever this module is
import public Native.Port
import public Native.Primitive

%default total

||| The 128-bit product of two words: its high word and its low word. The
||| body is its meaning, the exact product taken apart; the native code
||| generator computes it as one multiplication, which gives both. Never
||| inlined, so that a call stays a call of it for a code generator to see.
export %noinline
mul128 : Primitive.FunctionTy (Primitive.signature Primitive.Mul128)
mul128 x y =
  let p = cast {to = Integer} x * cast y
  in (cast (prim__shr_Integer p 64), cast p)
