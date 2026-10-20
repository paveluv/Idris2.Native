||| The double nearest a decimal of at most 19 digits (`nearest`): `w *
||| 10^q`, rounded to nearest, ties to even, as IEEE 754 reads a decimal.
||| By Clinger's fast path where `w` and `10^q` are both doubles, and
||| otherwise by Eisel and Lemire's algorithm as fast_float computes it,
||| which Mushtak and Lemire (2023) prove needs no fallback for such a
||| decimal. Pure: it reads only the powers of ten, tables, and multiplies by
||| the primitive `mul128`.
module Native.Support.Double.Nearest

import Native.Support.Double.PowerOfTen

import Native.Primitive.DoubleBits
import Native.Primitive.Mul128
import Native.Runtime.Bits
import Native.Table

%default total

||| 10^k as a double, k from 0 to 22, every one of them a double exactly.
export covering
exactPowerOfTen : Table 0 22 Double
exactPowerOfTen k _ = cast (power k)
  where
    power : Int -> Integer
    power 0 = 1
    power j = 10 * power (j - 1)

||| The bits of the double nearest `w * 10^q`, `w` from 1 below 2^64, by
||| Eisel and Lemire: the top bits of `w` times the 128-bit significand of
||| 5^q, a second word of it where the first leaves the rounding unsure,
||| rounded to nearest, ties to even; a subnormal, zero or infinity where
||| the result is one. The significand of 5^q is fast_float's: the table's
||| rounded down, plus one for q from -27 to -1, as its proof assumes.
export covering
eiselLemire : (w : Bits64) -> (q : Int) -> Bits64
eiselLemire w q =
  if w == 0 || q < -342 then 0
  else if q > 308 then 0x7FF0000000000000
  else
    let lz = leadingZeros w
        w' = w `shiftL` lz
        (ph, pl) = product w'
        upperbit = ph `shiftR` 63
        shift = upperbit + 9
        mantissa = ph `shiftR` shift
        power2 = power q + cast upperbit - cast lz + 1023
    in if power2 <= 0 then subnormal ph shift mantissa power2
      else normal ph pl shift mantissa power2
  where
    ||| floor(q * log2(5)) + q + 63, for q from -400 to 350.
    power : Int -> Int
    power k = prim__shr_Int ((152170 + 65536) * k) 16 + 63

    ||| The 128-bit significand of 5^q as fast_float has it.
    covering
    fiveTo : Int -> (Bits64, Bits64)
    fiveTo k with (-342 <= k && k <= 326) proof inside
      _ | True = case PowerOfTen.powerOfTen k inside of
        (h, l) => if -27 <= k && k <= -1 then (if l == 0xFFFFFFFFFFFFFFFF then h + 1 else h, l + 1)
          else (h, l)
      -- lint: allow trust-escape: unreached, as q is from -342 to 308 here
      _ | False =
        assert_total
          (idris_crash "Native.Support.Double.Nearest.fiveTo: an index outside the powers of ten")

    ||| `w` times 5^q, its top 128 bits: the second word of the power only
    ||| where the first product's low 9 bits of its high word are all ones.
    covering
    product : Bits64 -> (Bits64, Bits64)
    product w' = case fiveTo q of
      (h5, l5) => case Primitive.Mul128.mul128 w' h5 of
        (fh, fl) =>
          if fh .&. 0x1FF /= 0x1FF then (fh, fl) else
            case Primitive.Mul128.mul128 w' l5 of
              (sh, _) => let fl' = fl + sh in (if sh > fl' then fh + 1 else fh, fl')

    ||| A subnormal, or zero: the mantissa shifted down by what the
    ||| exponent lacks, then rounded; a carry into bit 52 makes it normal.
    subnormal : (ph, shift, mantissa : Bits64) -> (power2 : Int) -> Bits64
    subnormal ph shift mantissa power2 =
      if negate power2 + 1 >= 64 then 0 else
        let m = mantissa `shiftR` cast (negate power2 + 1)
            m' = (m + (m .&. 1)) `shiftR` 1
        in if m' < 0x10000000000000 then m' else m' .|. 0x10000000000000

    ||| A normal double: rounded half up, but to even where the product was
    ||| exact and fell halfway, which needs 5^q in one word, q from -4 to 23.
    normal : (ph, pl, shift, mantissa : Bits64) -> (power2 : Int) -> Bits64
    normal ph pl shift mantissa power2 =
      let tie = pl <= 1 && q >= -4 && q <= 23 && mantissa .&. 3 == 1 && (mantissa `shiftL` shift)
            == ph
          m = if tie then mantissa .&. 0xFFFFFFFFFFFFFFFE else mantissa
          m' = (m + (m .&. 1)) `shiftR` 1
          (m'', p') = if m' >= 0x20000000000000 then (0x10000000000000, power2 + 1)
            else (m', power2)
      in if p' >= 0x7FF then 0x7FF0000000000000
         else (m'' .&. 0xFFFFFFFFFFFFF) .|. (cast p' `shiftL` 52)

    ||| How many zero bits lead a nonzero word: a binary search by halves.
    leadingZeros : Bits64 -> Bits64
    leadingZeros x =
      let (x1, n1) = step x 32 0
          (x2, n2) = step x1 16 n1
          (x3, n3) = step x2 8 n2
          (x4, n4) = step x3 4 n3
          (x5, n5) = step x4 2 n4
          (_, n6) = step x5 1 n5
      in n6
      where
        -- if the word's top `bits` are zero, shift them out and count them
        step : Bits64 -> (bits, n : Bits64) -> (Bits64, Bits64)
        step y bits n = if y `shiftR` (64 - bits) == 0 then (y `shiftL` bits, n + bits) else (y, n)

||| The bits of the double nearest `w * 10^q`, `w` below 2^64: by Clinger's
||| fast path where `w` is at most 2^53 and q from -22 to 22, since then `w`
||| and `10^|q|` are doubles and one multiplication or division rounds the
||| product as IEEE 754 does; else by Eisel and Lemire.
export covering
nearest : (w : Bits64) -> (q : Int) -> Bits64
nearest w q =
  if w <= 0x20000000000000 && q >= -22 && q <= 22
     then Primitive.DoubleBits.doubleBits (clinger (cast {to = Double} w) q)
     else eiselLemire w q
  where
    covering
    clinger : Double -> Int -> Double
    clinger x k with (0 <= k && k <= 22) proof inside
      _ | True = x * exactPowerOfTen k inside
      _ | False with (0 <= negate k && negate k <= 22) proof inside'
        _ | True = x / exactPowerOfTen (negate k) inside'
        -- lint: allow trust-escape: unreached, as q is from -22 to 22 here
        _ | False =
          assert_total
            (idris_crash "Native.Support.Double.Nearest.clinger: a power outside the exact ones")
