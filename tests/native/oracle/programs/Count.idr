-- The example every lowering and target must render: an allocation, a
-- non-tail call and tail calls. wrap n is 2n + 1. The inner `count n 1` is
-- not a tail call: its continuation, an object on the heap, holds `m` until
-- it returns, and the outer call is a tail call, a jump. StatusCount is the
-- same program, reporting through its exit status.
module Main

count : Int -> Int -> Int
count 0 acc = acc
count n acc = count (n - 1) (acc + 1)

wrap : Int -> Int
wrap n = case the (List Int) [n] of
  (m :: _) => count m (count n 1)
  [] => 0

main : IO ()
main = printLn (map wrap [0, 1, 2, 3, 10])
