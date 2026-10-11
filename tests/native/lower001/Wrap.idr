-- The shared example, as Idris source: count counts n down by tail calls;
-- wrap allocates a cell, makes a non-tail call while the cell is live, and
-- tail-calls count. `first` is not inlined, so the cell is not optimised
-- away.
--
-- Ordinary code holds every value in one uniform representation, a machine
-- word: an `Int` that fits in 63 bits is a fixnum, the integer tagged in the
-- word itself, and any other is a pointer to a boxed 64-bit integer. So
-- `count`'s `n - 1` and `acc + 1` each ask which an argument is, and box a
-- result that leaves the fixnum range.
--
-- Ordinary code keeps no machine stack. A non-tail call's continuation,
-- what is left to do when it returns, is an object on the heap, which holds
-- the values live across the call; a tail call passes its caller's
-- continuation on, and is a jump. So `wrap` runs as if written in
-- continuation-passing style, `k` being its own continuation:
--
--   wrap n k = let cell = n :: Nil in
--              count n 1 (\r => first cell (\m => count m r k))
--
-- The first continuation holds `cell`, the second `r`. `Nil`, a
-- constructor without fields, is one static object that every use shares.
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
