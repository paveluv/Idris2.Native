-- Tables: functions of the integers from `lo` to `hi`, whose values the
-- native code generator computes when it compiles the program, into
-- read-only data, so that each call is a load. Chez compiles the body and
-- runs it at each call, which is the table's meaning; the two print the
-- same, so the expected output holds the same lines twice.
module Main

import Native.Support.Double.PowerOfTen
import Native.Table

-- A table of the program's own, of doubles: the compiler computes 2^-k for
-- each k from 0 to 4, so the program holds five doubles, in order.
halves : Table 0 4 Double
halves k _ = 1.0 / cast (prim__shl_Int 1 k)

-- A flat function that reads a row of `powerOfTen`. The test of the index
-- gives the proof `inside` that it is in the range, which the call needs
-- and which costs nothing at run time; the call is the table's address,
-- the row's offset from it, and two loads, as if written
--
--   foldRow : Int -> Bits64
--
-- over the two words of the row.
%cg native flat Main.foldRow
foldRow : Int -> Bits64
foldRow k with (-342 <= k && k <= 326) proof inside
  _ | True = case powerOfTen k inside of
    (high, low) => high + low
  _ | False = 0

-- A flat function that reads the doubles, scaled to an integer: the native
-- code generator does not lower a double constant in ordinary code yet, so
-- the arithmetic on them is flat. Each row is one double, loaded as one.
%cg native flat Main.scaledHalf
scaledHalf : Int -> Int
scaledHalf k with (0 <= k && k <= 4) proof inside
  _ | True = cast (halves k inside * 1024.0)
  _ | False = -1

main : IO ()
main = do
  -- ordinary code reads a table through the boundary of its flat form; a
  -- literal index's proof is `Refl`, since the test reduces
  printLn (powerOfTen (-342) Refl)
  printLn (powerOfTen (-1) Refl)
  printLn (powerOfTen 0 Refl)
  printLn (powerOfTen 55 Refl)
  printLn (powerOfTen 56 Refl)
  printLn (powerOfTen 326 Refl)
  traverse_ (\k => printLn (foldRow k)) [-343, -342, 0, 308, 326, 327]
  traverse_ (\k => printLn (scaledHalf k)) [-1, 0, 1, 4, 5]
