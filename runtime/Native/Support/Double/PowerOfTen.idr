||| The powers of ten as a table (`powerOfTen`), which the conversions
||| between doubles and their decimal text multiply by: computed when a
||| program that uses them is compiled, each a load where it runs.
module Native.Support.Double.PowerOfTen

-- lint: allow public-import: the table's type reduces only where its
-- reading is visible, so it is wherever this module is
import public Native.Table

%default total

||| The 128-bit significand of 10^k, rounded down: the high word and the low
||| word of the number m, 2^127 <= m < 2^128, such that 10^k = m * 2^e
||| exactly for some e, or the largest such m below it where there is none.
||| 10^k is 5^k * 2^k, so its significand is 5^k's: exact for k from 0 to
||| 55, where 5^k fits in 128 bits; for a negative k, 2^b / 5^-k for the b
||| that puts the quotient's top bit at 127. The range is what both
||| conversions reach: printing from 10^-292 to 10^326, reading from 10^-342
||| to 10^308.
export covering
powerOfTen : Table (-342) 326 (Bits64, Bits64)
powerOfTen k _ =
  let m = significand (cast k)
  in (cast (prim__shr_Integer m 64), cast m)
  where
    ||| The number of bits of a positive integer below 2^1024: the place of
    ||| its top bit, plus one, found by halving the shift from 512.
    bitLength : Integer -> Integer
    bitLength v = go 512 0 v
      where
        go : (shift, below : Integer) -> Integer -> Integer
        go 0 below _ = below + 1
        go shift below w =
          let w' = prim__shr_Integer w shift
              above = w' > 0
          in go (shift `div` 2) (if above then below + shift else below) (if above then w' else w)

    ||| b to the power e, for e >= 0, by squaring.
    power : (b, e : Integer) -> Integer
    power b 0 = 1
    power b e =
      let h = power b (e `div` 2)
          h2 = h * h
      in if e `mod` 2 == 0 then h2 else h2 * b

    ||| The significand of 10^k, as one integer.
    significand : Integer -> Integer
    significand k =
      if k >= 0
         then let v = power 5 k
                  b = bitLength v
              in if b <= 128 then prim__shl_Integer v (128 - b) else prim__shr_Integer v (b - 128)
         else let d = power 5 (negate k)
              in prim__shl_Integer 1 (bitLength d + 127) `div` d
