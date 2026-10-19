||| A double's bits and the double of bits (`doubleBits`, `bitsDouble`),
||| primitives (`Native.Primitive` says what one is).
module Native.Primitive.DoubleBits

-- lint: allow public-import: the primitives' types, written by their
-- signatures, reduce only where the signatures and their reading are
-- visible, so they are wherever this module is
import public Native.Port
import public Native.Primitive

%default total

||| 2^e as a double, by halving or doubling 1.0: exact for e from -1074 to
||| 1023, since a power of two in that range is a double.
pow2 : Int -> Double
pow2 e = if e >= 0 then up e 1.0 else down e 1.0
  where
    up : Int -> Double -> Double
    up 0 x = x
    -- lint: allow trust-escape: e' is positive here, so e' - 1 is nearer 0
    up e' x = up (assert_smaller e' (e' - 1)) (x * 2.0)

    down : Int -> Double -> Double
    down 0 x = x
    -- lint: allow trust-escape: e' is negative here, so e' + 1 is nearer 0
    down e' x = down (assert_smaller e' (e' + 1)) (x / 2.0)

||| A double's 64 bits, as IEEE 754 lays them out: the sign, the 11 bits of
||| the biased exponent, the 52 of the fraction. The body is its meaning,
||| taken apart by exact arithmetic on doubles: a power of two scales a
||| double exactly. A NaN's bits are the one quiet NaN's, whatever its
||| payload, which the body cannot see; the native code generator moves the
||| bits as they are, one instruction.
export %noinline
doubleBits : Primitive.FunctionTy (Primitive.signature Primitive.DoubleBits)
doubleBits x =
  if x /= x then 0x7FF8000000000000
  else
    let negative = x < 0.0 || (x == 0.0 && 1.0 / x < 0.0)
        sign : Bits64 = if negative then 0x8000000000000000 else 0
        a = if negative then negate x else x
    in sign + magnitude a
  where
    -- the place of a positive double's top bit: 2^e <= a < 2^(e+1)
    place : Double -> Int
    place a = if a >= 2.0 then high a 0 else low a 0
      where
        high, low : Double -> Int -> Int
        -- lint: allow trust-escape: halving a finite double of at least 2 reaches below 2 within
        -- 1024 steps
        high b e = if b >= 2.0 then high (assert_smaller b (b / 2.0)) (e + 1) else e
        -- lint: allow trust-escape: doubling a positive double below 1 reaches 1 within 1075 steps
        low b e = if b < 1.0 then low (assert_smaller b (b * 2.0)) (e - 1) else e

    -- the bits of a double that is not negative
    magnitude : Double -> Bits64
    magnitude a =
      if a == 0.0 then 0
      else if a > 1.7976931348623157e308 then 0x7FF0000000000000
      else
        let e = place a
        in if e < -1022
              then cast {to = Bits64} (cast {to = Integer} (a * pow2 1022 * pow2 52))
              else prim__shl_Bits64 (cast (e + 1023)) 52
                     + cast {to = Bits64}
                       (cast {to = Integer} ((a * pow2 (negate e) - 1.0) * pow2 52))

||| The double of 64 bits, as IEEE 754 lays them out. The body is its
||| meaning, put together by exact arithmetic on doubles; every NaN's bits
||| give the quiet NaN, since a double that the body makes has no other.
export %noinline
bitsDouble : Primitive.FunctionTy (Primitive.signature Primitive.BitsDouble)
bitsDouble w =
  let sign = if prim__shr_Bits64 w 63 == 1 then -1.0 else 1.0
      e = cast {to = Int} (prim__and_Bits64 (prim__shr_Bits64 w 52) 0x7FF)
      m = cast {to = Double} (cast {to = Integer} (prim__and_Bits64 w 0xFFFFFFFFFFFFF))
  in if e == 0x7FF then (if m == 0.0 then sign / 0.0 else 0.0 / 0.0)
     else if e == 0 then sign * (m * pow2 (-1074))
     else sign * ((pow2 52 + m) * pow2 (e - 1075))
