-- The shared example, as Idris source: count counts n down by tail calls;
-- wrap allocates a cell, makes a non-tail call while the cell is live, and
-- tail-calls count. `first` is not inlined, so the cell is not optimised
-- away.
module Main

import System

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
main = exitWith (ExitFailure (wrap 2))
