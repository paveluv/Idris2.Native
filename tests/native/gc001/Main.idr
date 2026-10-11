-- A program that allocates far more than its heap holds, under a window
-- of 4 KiB so that the slow path runs often: a list kept live across much
-- garbage, and a loop that builds and sums short lists two thousand times.
-- Every object is a constructor allocated by the inline bump; when the
-- window is out, the runtime's slow path collects once the heap has grown
-- past twice what the last collection left, copying what is reachable from
-- the current continuation and the root buffer, and the program never sees
-- the difference. The exit status is 0 when the sums are right and at
-- least one collection ran, which the runtime counts.
module Main

import Data.So
import Runtime.Space
import System

exitCode : Int -> IO ()
exitCode n = case choose (n == 0) of
  Left _ => exitSuccess
  Right _ => exitWith (ExitFailure n)

build : Int -> List Int -> List Int
build 0 acc = acc
build n acc = build (n - 1) (n :: acc)

churn : Int -> Int -> Int
churn 0 acc = acc
churn n acc = churn (n - 1) (acc + sum (build 50 []))

main : IO ()
main = do
  let keep = build 1000 []
  let r = churn 2000 0
  c <- collectionCount
  exitCode (if sum keep == 500500 && r == 2000 * 1275 && c > 0 then 0 else 1)
