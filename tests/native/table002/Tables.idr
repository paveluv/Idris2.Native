-- Tables (`Native.Support.Table`): functions of the integers from `lo` to
-- `hi`, made once as the words of their rows, so that a call of one is a
-- read of its row. Marked static, a table is made when the native code
-- generator compiles the program, as one object of the image's read-only
-- data, and a flat function reads a row as loads from the object's
-- address, with no call. Chez makes it once, before `main`, and reads its
-- words by their meaning, the buffer's. They print the same, so the
-- expected output holds the same lines three times: native, Chez, and
-- native under the encoding whose pointers carry a tag.
--
-- Three of the tables have the row types and the ranges of the runtime's
-- tables, not their rows: those of its powers of ten, pairs of words from
-- 10^-342 to 10^326; of its exact powers of ten, doubles from 10^0 to
-- 10^22; and of its error messages' text, one word a row from 0 to 937.
module Main

import Data.IORef
import Native.Support.Table
import Native.Support.Table.Row

%default covering

%cg native static Main.pairs Main.singles Main.halves Main.arounds Main.fromLeast
%cg native flat Main.sumPair Main.single Main.scaledHalf
%cg native flat Main.pairAt Main.singleAt Main.halfAt Main.passedAt Main.aroundAt

-- Rows of two words, the row's number from 0 and the square of its index:
-- as if written
--
--   pairs = <a BYTES object: its header, then the words 0, 116964, 1,
--            116281, ..., 668, 106276>
--
-- 669 rows of two words, the row of -342 first.
pairs : Table (-342) 326 (Bits64, Bits64)
pairs = tabulate (\k => (cast (k + 342), cast (k * k)))

-- Rows of one word, `3 * k + 1`: 938 words, 1, 4, ..., 2812. Only flat
-- code reads it, so that the code generator finds it read only in the
-- flat functions' forms, and makes it all the same.
singles : Table 0 937 Bits64
singles = tabulate (\k => cast (3 * k + 1))

-- Rows of one double, 2^-k: 23 words, the bits of 1.0, 0.5, ..., 2^-22.
halves : Table 0 22 Double
halves = tabulate (\k => 1.0 / cast (prim__shl_Int 1 k))

-- A row read where a test of the index proves it inside the range, and 0
-- outside: in surface Idris,
--
--   sumPair k = if -342 <= k && k <= 326
--                 then let (h, l) = <the two words at pairs + 8 + 16 * (k + 342)>
--                      in h + l
--                 else 0
--
-- the table's address and two loads; the test is two calls of `<=`.
sumPair : Int -> Bits64
sumPair k with (-342 <= k && k <= 326) proof inside
  _ | True = case Table.index pairs k inside of (h, l) => h + l
  _ | False = 0

-- A word, or 0 outside the range.
single : Int -> Bits64
single k with (0 <= k && k <= 937) proof inside
  _ | True = Table.index singles k inside
  _ | False = 0

-- A double, scaled to an integer, 2^(22 - k); -1 outside the range.
scaledHalf : Int -> Int
scaledHalf k with (0 <= k && k <= 22) proof inside
  _ | True = cast (Table.index halves k inside * 4194304.0)
  _ | False = -1

-- The reads alone, each given the proof by its caller, so that the flat
-- function is nothing but the read: the row of two words given back as
-- two registers, as if written
--
--   pairAt k = (<the word at pairs + 8 + 8 * (2 * k + 684)>,
--               <the word at pairs + 8 + 8 * (2 * k + 685)>)
--
-- with no call: the index `2 * k`, then each word at a constant
-- displacement, `- lo * 2` words and the word's number past the header.
pairAt : (k : Int) -> (0 inside : (-342 <= k && k <= 326) = True) -> (Bits64, Bits64)
pairAt k inside = Table.index pairs k inside

-- One word: `<the word at singles + 8 + 8 * k>`.
singleAt : (k : Int) -> (0 inside : (0 <= k && k <= 937) = True) -> Bits64
singleAt k inside = Table.index singles k inside

-- One double: the word at `halves + 8 + 8 * k`, then the double of its
-- bits, which is the word moved, not converted.
halfAt : (k : Int) -> (0 inside : (0 <= k && k <= 22) = True) -> Double
halfAt k inside = Table.index halves k inside

-- A table given as an argument, one register, the object as ordinary
-- code holds it: the same loads from it as from a static table's address.
passedAt : Table (-342) 326 (Bits64, Bits64) -> (k : Int) ->
           (0 inside : (-342 <= k && k <= 326) = True) -> (Bits64, Bits64)
passedAt t k inside = Table.index t k inside

-- A row type whose `row` asks for words outside its row, which no
-- implementation should: rows of one word, the row of its words the word
-- before it and the word after it, as if written
--
--   row w = MkAround (w (-1), w 1)
--
-- `index` gives 0 for a word number outside the row, never a load, so
-- that a row of it is (0, 0) wherever it is read, where loads would give
-- the words of the rows before and after it.
record Around where
  constructor MkAround
  pair : (Bits64, Bits64)

%inline
Row Around where
  rowWords = 1
  word x _ = fst x.pair
  row w = MkAround (w (-1), w 1)

-- Ten rows of one word, 100 to 109.
arounds : Table 0 9 Around
arounds = tabulate (\k => MkAround (cast (k + 100), 0))

-- A row read by flat code, where the word numbers are constants, so that
-- the tests of them are computed as the program is compiled: the read is
-- `(0, 0)`, and no load.
aroundAt : (k : Int) -> (0 inside : (0 <= k && k <= 9) = True) -> (Bits64, Bits64)
aroundAt k inside = (Table.index arounds k inside).pair

-- Three rows from the least `Int`, unmarked, each its number from 0: in
-- surface Idris, `least = <the words 0, 1, 2>`.
least : Table (-9223372036854775807 - 1) (-9223372036854775807 + 1) Bits64
least = tabulate (\k => cast (k + 9223372036854775807 + 1))

-- A table made of `least`'s rows when the native code generator compiles
-- the program: row `k` of it is row `-2^63 + k` of `least`, the `k`-th.
-- A read of that row loads at the index `(-2^63 + k) * 1` and the
-- displacement `- lo * 1`, which `negate` wraps around to -2^63 too:
-- summed as `Int`s, which wrap around, they give word `k`, as the load's
-- address does when the program runs.
fromLeast : Table 0 2 Bits64
fromLeast = tabulate (\k => case k of
                              0 => Table.index least (-9223372036854775807 - 1) Refl
                              1 => Table.index least (-9223372036854775807) Refl
                              _ => Table.index least (-9223372036854775807 + 1) Refl)

-- A range far backwards, from the greatest `Int` down to the least: no
-- rows, as for any `hi` below `lo`, however far below, so that it is made
-- and the program goes on.
backwards : Table 9223372036854775807 (-9223372036854775807 - 1) Bits64
backwards = tabulate (\k => cast k)

-- Something of a table, which takes it from its cell: natively an
-- unmarked table's first read, which makes it.
%noinline
touched : Table lo hi r -> String
touched _ = "a table made"

-- How many times `counted`'s meaning has been called.
made : IORef Int
made = unsafePerformIO (newIORef 0)

-- Three rows of two words, `(k, 10 * k)`, each word made by a call of the
-- meaning, which counts it: a table no mark names and no flat code reads,
-- so that every code generator makes it as the program runs. In surface
-- Idris,
--
--   counted = tabulate (\k => do made := made + 1; (k, 10 * k))
--
-- Idris keeps a constant's value once it is made: natively from its first
-- read, on Chez from before `main`. So the count after three reads is its
-- six words, made once, on every code generator.
counted : Table 0 2 (Bits64, Bits64)
counted = tabulate (\k => unsafePerformIO (do modifyIORef made (+ 1); pure (cast k, cast k * 10)))

main : IO ()
main = do
  -- flat reads at both ends of each range, and just outside them
  printLn (map sumPair [-343, -342, -1, 0, 325, 326, 327])
  printLn (map single [-1, 0, 1, 936, 937, 938])
  printLn (map scaledHalf [-1, 0, 1, 21, 22, 23])
  -- the rows as the flat reads give them back; a literal index's proof is
  -- `Refl`, since the test reduces
  printLn (pairAt (-342) Refl, pairAt 0 Refl, pairAt 326 Refl)
  printLn (singleAt 0 Refl, singleAt 937 Refl)
  printLn (halfAt 0 Refl, halfAt 3 Refl, halfAt 22 Refl)
  printLn (passedAt pairs (-342) Refl, passedAt pairs 326 Refl)
  -- ordinary code's reads: natively each word a call of the load's flat
  -- form, through its boundary; on Chez the load's meaning, the buffer's
  printLn (Table.index pairs (-342) Refl, Table.index pairs 326 Refl)
  printLn (Table.index halves 1 Refl, Table.index halves 22 Refl)
  -- a row asking for the words outside it, read by flat code and by
  -- ordinary code: 0 for each, never a load
  printLn (aroundAt 5 Refl, (Table.index arounds 4 Refl).pair)
  -- the table made of `least`'s rows, read: 0, 1 and 2
  printLn (Table.index fromLeast 0 Refl, Table.index fromLeast 1 Refl, Table.index fromLeast 2 Refl)
  -- the range far backwards, made: no rows
  putStrLn (touched backwards)
  -- `counted` read three times, its words made once: a count of 6
  printLn (Table.index counted 0 Refl, Table.index counted 1 Refl, Table.index counted 2 Refl)
  printLn !(readIORef made)
