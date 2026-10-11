-- Int arithmetic, across the edge of the 63-bit fixnum range, where the
-- native backend changes from tagged to boxed integers. An `Int` is 64 bits;
-- a uniform value is one word, which holds the integer itself, tagged, when
-- it fits in 63 bits, and otherwise points to a box of 64. Each operation
-- checks its fixnum result for overflow, and boxes it when it overflows.
module Main

||| 2^62 - 1, the largest fixnum.
big : Int
big = 4611686018427387903

main : IO ()
main = do
  printLn (2 + 3 * 7 - 4)
  printLn (div 17 5, mod 17 5)
  printLn (div (-17) 5, mod (-17) 5)
  printLn (big + 1)
  printLn (big * 2 + 1)
  printLn (negate big - 1)
  printLn (negate big - 2)
  printLn (big + 1 - 1 == big)
  printLn (compare big (big + 1), max (big + 1) big)
