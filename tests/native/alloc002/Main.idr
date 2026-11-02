-- Ordinary programs under an 8-byte allocation window, so that every
-- allocation takes the slow path every site shares, and the collector runs
-- again and again, moving what is live.
--
-- An allocation site's slow path saves what is GC-visible and live across
-- the allocation, what the code after the allocation still reads, and
-- reloads it. In
--
--   pairUp a b = (a + b, [a, b, a * b])
--
-- the list is built from its end, so `a * b :: []` is allocated while `a`
-- and `b` are still to be stored in the cells before it, and the pair's
-- cell while the sum and the list are; each of these values is GC-visible,
-- a fixnum or a pointer, and if the collector moves the object a pointer
-- points to, the slow path reloads the pointer as the collector left it.
-- A double is raw while it is computed, before its box is allocated:
--
--   spread a b = [a + b, a * b, a - b]
--
-- allocates the box of `a - b` while the result itself, a raw double, is
-- live: the collector must not take it for a pointer, and it stays in its
-- slot, which nothing the slow path runs writes. `Wide.wide`
-- binds 300 values and builds the list of them, so the list's first cell
-- is allocated with all 301 live, and the slots of a function that binds
-- 300 values go past 255: its table's entries take 16 bits.
--
-- The exit status is 0 when every result is right and collections ran.
module Main

import Data.So
import Native.Runtime.Space
import System
import Wide

exitCode : Int -> IO ()
exitCode n = case choose (n == 0) of
  Left _ => exitSuccess
  Right _ => exitWith (ExitFailure n)

pairUp : Integer -> Integer -> (Integer, List Integer)
pairUp a b = (a + b, [a, b, a * b])

spread : Double -> Double -> List Double
spread a b = [a + b, a * b, a - b]

shifts : Bits64 -> List Bits64
shifts w = [w + 1, w * 3, w - 1]

-- 1 to n, built from the end: each cell allocated with the rest live
upTo : Integer -> List Integer -> List Integer
upTo 0 acc = acc
upTo n acc = upTo (n - 1) (n :: acc)

-- the pairs and the lists of 1 to 2,000, made and summed
churn : Integer -> Integer -> Integer
churn 0 acc = acc
churn n acc =
  let (s, xs) = pairUp n (n + 1) in
  churn (n - 1) (acc + s + sum xs)

main : IO ()
main = do
  let w = wide 1
  let r = churn 2000 0
  let ds = spread 1.5 0.25
  let bs = shifts 41
  let keep = upTo 1000 []
  c <- collectionCount
  let ok = length w == 301 && sum w == 45451
           && r == expected
           && ds == [1.75, 0.375, 1.25]
           && bs == [42, 123, 40]
           && sum keep == 500500
           && c > 0
  exitCode (if ok then 0 else 1)
  where
    -- the sum of (n + n + 1) + (n + (n + 1) + n (n + 1)) for n from 1 to
    -- 2,000: 4n + 2 + n^2 + n, so 5 n(n+1)/2 + 2n + n(n+1)(2n+1)/6
    expected : Integer
    expected =
      let n = the Integer 2000 in
      5 * n * (n + 1) `div` 2 + 2 * n + n * (n + 1) * (2 * n + 1) `div` 6
