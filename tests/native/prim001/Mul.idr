-- The backend's primitive `mul128`, the 128-bit product of two words, on
-- both code generators. Chez compiles its body, which is its meaning: the
-- exact product of the two as `Integer`s, taken apart into its high word
-- and its low word. The native code generator never compiles the body: it
-- computes each call as one `mul`, which gives both words at once. The two
-- print the same, so the expected output holds the same lines twice.
module Main

import Native.Primitive.Mul128

-- A flat function returning both words: two registers, as if written
--
--   product : Bits64 -> Bits64 -> (Bits64, Bits64)
--
-- with the pair's words in registers, the call of `mul128` the instruction
-- itself.
%cg native flat Main.product
product : Bits64 -> Bits64 -> (Bits64, Bits64)
product x y = mul128 x y

-- A flat function that takes the product apart: the case on the pair binds
-- its two registers, and the sum wraps, as `Bits64` does.
%cg native flat Main.sumHalves
sumHalves : Bits64 -> Bits64 -> Bits64
sumHalves x y = case mul128 x y of
  (h, l) => h + l

-- The edges: zero, one, the largest word, a power of two either side of a
-- word's halves, and two patterns whose product carries through every
-- column.
cases : List (Bits64, Bits64)
cases =
  [ (0, 0), (1, 18446744073709551615), (18446744073709551615, 18446744073709551615)
  , (4294967296, 4294967296), (9223372036854775808, 2)
  , (0x123456789ABCDEF0, 0xFEDCBA9876543210), (3, 0x5555555555555556) ]

main : IO ()
main = do
  -- ordinary code calls the primitive too: through the boundary of its
  -- flat form, which applies it
  traverse_ (\(x, y) => printLn (mul128 x y)) cases
  traverse_ (\(x, y) => printLn (product x y)) cases
  traverse_ (\(x, y) => printLn (sumHalves x y)) cases
