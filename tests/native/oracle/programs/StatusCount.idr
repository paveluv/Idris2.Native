-- The shared example, reporting through the exit status: an allocation, a
-- non-tail call with the cell live across it, and tail calls. wrap 2 is 5.
-- The status is wrap 2 + wrap 50 = 5 + 101 = 106. lower001 and render001
-- show how `wrap` is compiled.
module Main

import Data.So
import System

exitCode : Int -> IO ()
exitCode n = case choose (n == 0) of
  Left _ => exitSuccess
  Right _ => exitWith (ExitFailure n)

count : Int -> Int -> Int
count 0 acc = acc
count n acc = count (n - 1) (acc + 1)

%noinline
first : List Int -> Int
first (m :: _) = m
first [] = 0

wrap : Int -> Int
wrap n = let cell = the (List Int) [n]
             r = count n 1
         in count (first cell) r

main : IO ()
main = exitCode (wrap 2 + wrap 50)
