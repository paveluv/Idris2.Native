||| Numbers as their bytes, low byte first (little-endian), each width's
||| as a list of so many bytes, a negative number's as two's complement;
||| and a number rounded up to a multiple.
module Native.Data.LittleEndian

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
