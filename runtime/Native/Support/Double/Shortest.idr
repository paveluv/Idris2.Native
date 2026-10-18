||| The shortest decimal of a double (`shortest`): the fewest significant
||| digits that read back to the same double, and of those the one closest
||| to it, by Jeon's Dragonbox (2020), as its reference implementation
||| computes it for IEEE 754's binary64 and rounding to nearest, ties to
||| even. Pure: it reads only the powers of ten, a table, and multiplies by
||| the primitive `mul128`.
module Native.Support.Double.Shortest

-- lint: allow public-import: the flat translation reaches through this module
-- (checking an importer's flat functions, it reaches this module's bodies,
-- which use them, so they are loaded wherever this module is)
import public Native.Primitive.Mul128
import public Native.Support.Double.PowerOfTen

import Native.Runtime.Bits

%default total

||| The shortest decimal of a positive finite double, of the fraction and
||| the biased exponent of its bits, `2^52 + fraction` scaled by
||| `2^(exponent - 1075)` (`fraction * 2^-1074` where the exponent is 0):
||| the decimal significand, without trailing zeros, and the power of ten
||| it is scaled by.
export covering
shortest : (fraction, exponent : Bits64) -> (Bits64, Int)
shortest f be =
  let isEven = f .&. 1 == 0
      twoFc = f `shiftL` 1
  in if be /= 0
        then (if twoFc == 0 then shorter (cast be - 1075) else normal (twoFc .|. (1 `shiftL` 53)) (cast be - 1075) isEven)
        else normal twoFc (-1074) isEven
  where
    ||| floor(e * log2(10)), for |e| <= 1233.
    floorLog2Pow10 : Int -> Int
    floorLog2Pow10 e = prim__shr_Int (e * 1741647) 19

    ||| floor(e * log10(2) - log10(4/3)), for e from -2985 to 2936.
    floorLog10Pow2MinusLog10_4Over3 : Int -> Int
    floorLog10Pow2MinusLog10_4Over3 e = prim__shr_Int (e * 631305 - 261663) 21

    ||| The cache of Dragonbox for 10^k, k from -292 to 326: the 128-bit
    ||| significand of 10^k rounded up, which is the table's rounded down plus
    ||| one wherever 10^k is not exact, outside k from 0 to 55.
    covering
    cache : Int -> (Bits64, Bits64)
    cache k with (-342 <= k && k <= 326) proof inside
      _ | True = case powerOfTen k inside of
        (h, l) => if 0 <= k && k <= 55 then (h, l) else (if l == 0xFFFFFFFFFFFFFFFF then h + 1 else h, l + 1)
      -- lint: allow trust-escape: unreached, as Dragonbox's indices for binary64 are from -292 to 326, inside the table's range
      _ | False = assert_total (idris_crash "Native.Support.Double.Shortest.cache: an index outside the powers of ten")

    ||| The high word of a 64-by-64-bit product.
    high : Bits64 -> Bits64 -> Bits64
    high x y = fst (mul128 x y)

    ||| A decimal significand without its trailing zeros, the exponent raised
    ||| by as many: a binary search of divisions by 10^8, 10^4, 10^2 and 10,
    ||| each a multiplication by the divisor's inverse modulo 2^64 and a
    ||| rotation, which is small exactly when the division is exact (Jeon's
    ||| rtz_benchmark).
    removeTrailingZeros : (Bits64, Int) -> (Bits64, Int)
    removeTrailingZeros (s, e) =
      let (s1, n1) = step s 28999941890838049 8 184467440738 0
          (s2, n2) = step s1 182622766329724561 4 1844674407370956 n1
          (s3, n3) = step s2 10330176681277348905 2 184467440737095517 n2
          (s4, n4) = step s3 14757395258967641293 1 1844674407370955162 n3
      in (s4, e + n4)
      where
        ||| The word rotated right by `n` bits, `n` from 1 to 63.
        rotateRight : Bits64 -> (n : Bits64) -> Bits64
        rotateRight x n = (x `shiftR` n) .|. (x `shiftL` (64 - n))

        step : Bits64 -> (inverse, shift, bound : Bits64) -> Int -> (Bits64, Int)
        step x inverse shift bound n =
          let r = rotateRight (x * inverse) shift
          in if r < bound then (r, n + cast shift) else (x, n)

    ||| A power of two, whose interval below is half the one above: the
    ||| candidates are its endpoints' integers, as Schubfach finds them.
    covering
    shorter : Int -> (Bits64, Int)
    shorter e =
      let minusK = floorLog10Pow2MinusLog10_4Over3 e
          beta = e + floorLog2Pow10 (negate minusK)
          (ch, _) = cache (negate minusK)
          shift = cast {to = Bits64} (11 - beta)
          xi0 = (ch - (ch `shiftR` 54)) `shiftR` shift
          zi = (ch + (ch `shiftR` 53)) `shiftR` shift
          -- the left endpoint is an integer only for exponents 2 and 3
          xi = if e >= 2 && e <= 3 then xi0 else xi0 + 1
          s = high zi 1844674407370955162
      in if s * 10 >= xi then removeTrailingZeros (s, minusK + 1) else
           let y = ((ch `shiftR` cast (10 - beta)) + 1) `shiftR` 1
               -- a tie, at exponent -77 alone, goes to the even one
               y' = if y .&. 1 /= 0 && e == -77 then y - 1 else if y < xi then y + 1 else y
           in (y', minusK)

    ||| floor(e * log10(2)), for |e| <= 2620.
    floorLog10Pow2 : Int -> Int
    floorLog10Pow2 e = prim__shr_Int (e * 315653) 20

    ||| The upper 128 bits of the 192-bit product of a word and a 128-bit
    ||| number, as its high word and its low word.
    upper128 : Bits64 -> (Bits64, Bits64) -> (Bits64, Bits64)
    upper128 x (ch, cl) = case mul128 x ch of
      (h, l) => let l' = l + high x cl in (if l' < l then h + 1 else h, l')

    ||| Of `2f * 2^beta * 10^k`, `beta` from 1 to 63: whether its integer part
    ||| is odd, and whether it is an integer.
    mulParity : (twoF : Bits64) -> (cache : (Bits64, Bits64)) -> (beta : Bits64) -> (Bool, Bool)
    mulParity twoF c beta = case lower128 twoF c of
      (h, l) => ((h `shiftR` (64 - beta)) .&. 1 /= 0, ((h `shiftL` beta) .|. (l `shiftR` (64 - beta))) == 0)
      where
        ||| The lower 128 bits of the 192-bit product of a word and a 128-bit
        ||| number, as its high word and its low word.
        lower128 : Bits64 -> (Bits64, Bits64) -> (Bits64, Bits64)
        lower128 x (ch, cl) = case mul128 x cl of
          (h, l) => (x * ch + h, l)

    ||| Any other double: the candidate of the larger divisor, 10^3, first,
    ||| then of the smaller, 10^2.
    covering
    normal : (twoFc : Bits64) -> Int -> (isEven : Bool) -> (Bits64, Int)
    normal twoFc e isEven =
      let minusK = floorLog10Pow2 e - 2
          c = cache (negate minusK)
          beta = e + floorLog2Pow10 (negate minusK)
          b = cast {to = Bits64} beta
          deltai = fst c `shiftR` (63 - b)
          (zi, zl) = upper128 ((twoFc .|. 1) `shiftL` b) c
          zIsInteger = zl == 0
          s = high zi 4722366482869645214 `shiftR` 8
          r = zi - 1000 * s
      in if r < deltai
            then (if r == 0 && zIsInteger && not isEven then smaller minusK c b (s - 1) 1000 deltai
                  else removeTrailingZeros (s, minusK + 3))
         else if r > deltai then smaller minusK c b s r deltai
         else case mulParity (twoFc - 1) c b of
           (xParity, xIsInteger) =>
             if xParity || (xIsInteger && isEven) then removeTrailingZeros (s, minusK + 3)
             else smaller minusK c b s r deltai
      where
        smaller : (minusK : Int) -> (Bits64, Bits64) -> (beta : Bits64) -> (s, r, deltai : Bits64) -> (Bits64, Int)
        smaller minusK c b s r deltai =
          let dist = r - (deltai `shiftR` 1) + 50
              approxYParity = (dist `xor` 50) .&. 1 /= 0
              -- dist / 100, and whether it divides: by 656 / 2^16 on 32 bits
              prod = (dist * 656) .&. 0xFFFFFFFF
              divisible = prod .&. 0xFFFF < 656
              s' = s * 10 + (prod `shiftR` 16)
          in if not divisible then (s', minusK + 2) else
               case mulParity twoFc c b of
                 (yParity, yIsInteger) =>
                   if yParity /= approxYParity then (s' - 1, minusK + 2)
                   else if s' .&. 1 /= 0 && yIsInteger then (s' - 1, minusK + 2)
                   else (s', minusK + 2)
          where
            xor : Bits64 -> Bits64 -> Bits64
            xor = prim__xor_Bits64
