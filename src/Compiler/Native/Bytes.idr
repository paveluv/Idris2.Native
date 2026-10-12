||| Little-endian byte serialisation shared by the encoder and the object
||| writers. Every target in scope is little-endian.
module Compiler.Native.Bytes

import public Data.Builder
import Data.List

%default total

||| Byte `i` of `x`, an integer in [0, 2^64): the word's bits shifted down,
||| the cast to a byte keeping the low eight. (Dividing the `Integer` by a
||| power of 256 cost a multiplication chain and two divisions per byte, a
||| quarter of the time of linking a large program.)
export
byteAt : Integer -> Nat -> Bits8
byteAt x i = cast (prim__shr_Bits64 (cast x) (cast (8 * i)))

norm : Integer -> Integer -> Integer
norm modulus x = if x < 0 then x + modulus else x

export
le8 : Int -> List Bits8
le8 x = [byteAt (norm 256 (cast x)) 0]

export
le16 : Int -> List Bits8
le16 x = let v = norm 65536 (cast x) in map (byteAt v) [0, 1]

export
le32 : Int -> List Bits8
le32 x = let v = norm 4294967296 (cast x) in map (byteAt v) [0, 1, 2, 3]

export
le64 : Integer -> List Bits8
le64 x = let v = norm 18446744073709551616 x in map (byteAt v) [0, 1, 2, 3, 4, 5, 6, 7]

||| `n` zero bytes.
export
zeros : Nat -> List Bits8
zeros n = replicate n 0

||| Round `x` up to a multiple of `a` (`a > 0`).
export
alignUp : Int -> Int -> Int
alignUp x a = ((x + a - 1) `div` a) * a

||| The IEEE 754 binary64 bit pattern of a double, as an unsigned integer:
||| what its eight bytes hold. Idris has no cast that reinterprets a double,
||| so the pattern is computed, by scaling by powers of two, which is exact.
||| Every NaN gives the quiet NaN with no payload.
export
doubleBits : Double -> Integer
doubleBits x =
    if x /= x then 0x7FF8000000000000
    else (if x < 0 || (x == 0 && 1 / x < 0) then 0x8000000000000000 else 0) + magnitude (abs x)
  where
    doubled : Nat -> Double -> Double
    doubled Z a = a
    doubled (S k) a = doubled k (a * 2)

    -- (m, e) with a = m * 2^e and 1 <= m < 2, for a normal double a
    normalise : Nat -> Double -> Integer -> (Double, Integer)
    normalise Z m e = (m, e)
    normalise (S k) m e =
      if m >= 2 then normalise k (m / 2) (e + 1)
      else if m < 1 then normalise k (m * 2) (e - 1)
      else (m, e)

    -- the pattern of a double that is not negative: 0; infinity; a
    -- subnormal, whose pattern is its value in units of 2^-1074; or a
    -- normal double, of a biased exponent and the fraction's 52 bits
    magnitude : Double -> Integer
    magnitude a =
      if a == 0 then 0
      else if a > 1.7976931348623157e308 then 0x7FF0000000000000
      else if a < 2.2250738585072014e-308 then cast (doubled 1074 a)
      else let (m, e) = normalise 2100 a 0 in
           (e + 1023) * 0x10000000000000 + cast ((m - 1) * 4503599627370496.0)

||| Bytes padded with zeros to a multiple of 8.
export
pad8 : List Bits8 -> List Bits8
pad8 bs = bs ++ zeros (cast (alignUp (cast (length bs)) 8 - cast (length bs)))
