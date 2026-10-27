-- The runtime's tables (`Native.Support.Table`), its powers of ten, and a
-- table of the program's own: each made once as the words of its rows,
-- marked static, so that the native code generator computes the rows as
-- it compiles the program, into read-only data. Flat code reads a row as
-- loads from the table's address; ordinary code, natively, by a call for
-- each word of the function Idris makes of the bound in `index`, which
-- compares the word number and loads the word. Chez makes each table
-- once, as a constant, and reads its words. The rows of all three are
-- compared, every one, with their meaning computed as the program runs.
-- The two code generators, and the native one under the encoding whose
-- pointers carry a tag, print the same, so the expected output holds the
-- same lines three times.
module Main

import Native.Support.Double.ExactPowerOfTen
import Native.Support.Double.PowerOfTen
import Native.Support.Table
import Native.Support.Table.Row

%default covering

%cg native static Main.halves

-- 2^-k, for k from 0 to 62: the meaning of the table `halves`.
half : Int -> Double
half k = 1.0 / cast (prim__shl_Int 1 k)

-- A table of the program's own, of doubles: the compiler computes 2^-k
-- (`half k`) for each k from 0 to 4, so the program holds five doubles,
-- in order, as if written
--
--   halves = <a BYTES object: its header, then the bits of 1.0, 0.5,
--             0.25, 0.125, 0.0625>
halves : Table 0 4 Double
halves = tabulate half

-- A flat function that reads a row of `powerOfTen`. The test of the index
-- gives the proof `inside` that it is in the range, which the read needs
-- and which costs nothing at run time; the read is the table's address,
-- the index `2 * k`, and two loads, as if written
--
--   foldRow k = if -342 <= k && k <= 326
--                 then <the word at powerOfTen + 8 + 8 * (2 * k + 684)>
--                      + <the word at powerOfTen + 8 + 8 * (2 * k + 685)>
--                 else 0
--
-- over the two words of the row, the high one first.
%cg native flat Main.foldRow
foldRow : Int -> Bits64
foldRow k with (-342 <= k && k <= 326) proof inside
  _ | True = case Table.index powerOfTen k inside of
    (high, low) => high + low
  _ | False = 0

-- A flat function that reads the doubles, scaled to an integer, as the
-- runtime's reading of a decimal reads its table of doubles: each row is
-- one double, loaded as its word, whose bits are the double's, as if
-- written
--
--   scaledHalf k = if 0 <= k && k <= 4
--                    then cast (<the double at halves + 8 + 8 * k> * 1024.0)
--                    else -1
%cg native flat Main.scaledHalf
scaledHalf : Int -> Int
scaledHalf k with (0 <= k && k <= 4) proof inside
  _ | True = cast (Table.index halves k inside * 1024.0)
  _ | False = -1

-- Whether row k of `powerOfTen`, as the table holds it, differs from
-- `significand k`, computed again as the program runs:
--
--   powerDiffers k = <the two words of row k> /= significand k
--
-- for k in the range; outside it, there is no row, and nothing differs.
powerDiffers : Int -> Bool
powerDiffers k with (-342 <= k && k <= 326) proof inside
  _ | True = Table.index powerOfTen k inside /= significand k
  _ | False = False

-- The same of `exactPowerOfTen` and `exact k`, doubles compared as such.
exactDiffers : Int -> Bool
exactDiffers k with (0 <= k && k <= 22) proof inside
  _ | True = Table.index exactPowerOfTen k inside /= exact k
  _ | False = False

-- The same of `halves` and `half k`.
halfDiffers : Int -> Bool
halfDiffers k with (0 <= k && k <= 4) proof inside
  _ | True = Table.index halves k inside /= half k
  _ | False = False

-- How many of the rows from `lo` to `hi` differ, as the line
-- "<table>: <count> rows differ".
differing : String -> (Int -> Bool) -> (lo, hi : Int) -> IO ()
differing table differs lo hi =
  putStrLn (table ++ ": " ++ show (length (filter differs [lo .. hi])) ++ " rows differ")

main : IO ()
main = do
  -- ordinary code reads the same object, natively each word by a call of
  -- the function Idris makes of the bound in `index`, where flat code
  -- loads it; a literal index's proof is `Refl`, since the test reduces
  printLn (Table.index powerOfTen (-342) Refl)
  printLn (Table.index powerOfTen (-1) Refl)
  printLn (Table.index powerOfTen 0 Refl)
  printLn (Table.index powerOfTen 55 Refl)
  printLn (Table.index powerOfTen 56 Refl)
  printLn (Table.index powerOfTen 326 Refl)
  traverse_ (\k => printLn (foldRow k)) [-343, -342, 0, 308, 326, 327]
  traverse_ (\k => printLn (scaledHalf k)) [-1, 0, 1, 4, 5]
  differing "powerOfTen" powerDiffers (-342) 326
  differing "exactPowerOfTen" exactDiffers 0 22
  differing "halves" halfDiffers 0 4
