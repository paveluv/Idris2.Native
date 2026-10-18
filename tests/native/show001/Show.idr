-- `show` of a double, natively: the shortest digits that read back to it
-- (Dragonbox, in the runtime's flat code, its powers of ten a table the
-- compiler computed), laid out as Chez lays them out. The output differs
-- from Chez's in two ways only, which dragonbox001 checks: an exact tie
-- between two shortest decimals is printed with the even digit, and a
-- subnormal without Chez's `|n` after it.
module Main

import Native.Primitive.DoubleBits

-- A double of its bits: a flat function, in which a double is a register
-- and `bitsDouble` the one instruction that moves the bits into it. As if
-- written
--
--   fromBits : Bits64 -> Double
--
-- over registers; ordinary code gets the double boxed, as it holds one.
%cg native flat Main.fromBits
fromBits : Bits64 -> Double
fromBits = bitsDouble

next : Bits64 -> Bits64
next x = x * 6364136223846793005 + 1442695040888963407

-- Zeros, the smallest and largest subnormals, the smallest normal, the
-- largest double, the infinities, two NaNs, and doubles at each layout:
-- 1.0, 0.1, 1e20, 1e-7, 0.001, 1e-4, 1e10, 1000000000.0, 2^53, -pi.
edges : List Bits64
edges = [0, 0x8000000000000000, 1, 0x8000000000000001, 0x000FFFFFFFFFFFFF, 0x0010000000000000, 0x7FEFFFFFFFFFFFFF,
         0x7FF0000000000000, 0xFFF0000000000000, 0x7FF8000000000000, 0xFFF8000000000001, 0x3FF0000000000000,
         0x3FB999999999999A, 0x4415AF1D78B58C40, 0x3E7AD7F29ABCAF48, 0x3F50624DD2F1A9FC, 0x3F1A36E2EB1C432D,
         0x4202A05F20000000, 0x41CDCD6500000000, 0x4340000000000000, 0xC00921FB54442D18]

loop : Nat -> Bits64 -> IO ()
loop Z _ = pure ()
loop (S n) x = do
  putStrLn (show (fromBits x))
  loop n (next x)

main : IO ()
main = do
  traverse_ (\b => putStrLn (show (fromBits b))) edges
  loop 500 777
