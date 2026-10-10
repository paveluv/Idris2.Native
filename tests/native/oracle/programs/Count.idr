-- The example every lowering and target must render: an allocation, a
-- non-tail call and tail calls. wrap n is 2n + 1.
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
