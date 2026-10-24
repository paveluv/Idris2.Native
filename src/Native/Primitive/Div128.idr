||| The division of a 128-bit number by a word (`div128`), a primitive
||| (`Native.Primitive` says what one is).
module Native.Primitive.Div128

-- lint: allow public-import: the primitive's type, written by its signature,
-- reduces only where the signature and its reading are visible, so they are
-- wherever this module is
import public Native.Port
import public Native.Primitive

%default total

||| The number of the high and the low word divided by the divisor: its
||| quotient and its remainder. The high word below the divisor, which the
||| call proves, makes the quotient a word, and the divisor no zero; the
||| machine's division faults otherwise. The body is its meaning, the exact
||| division taken apart; the native code generator computes it as one
||| division, which gives both. Never inlined, so that a call stays a call
||| of it for a code generator to see.
export %noinline
div128 : Primitive.FunctionTy (Primitive.signature Primitive.Div128)
div128 high low divisor _ =
  let n = prim__shl_Integer (cast {to = Integer} high) 64 + cast low
      d = cast {to = Integer} divisor
  in (cast (n `div` d), cast (n `mod` d))
