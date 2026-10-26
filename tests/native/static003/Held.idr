-- A list marked static that the program reads under a heap limit its
-- cells would exceed: natively the cells are in the image's read-only
-- data, which the heap does not hold, so the program allocates none of
-- them and runs under the limit, collecting as it allocates. As if written
--
--   squares = <the first of 3000 cells in the image: 1 :: 4 :: ... :: Nil>
--
-- The limit, 64 KiB, lets the copying collector hold 32 KiB of data, and
-- the 3000 cells, 24 bytes each, are 72000. A copy of the program without
-- the mark computes the list on its first use and keeps it, as every
-- constant is kept, so it holds the cells while it runs, exceeds the
-- limit and ends with a message; the same copy under no limit prints what
-- this program does.
module Main

import Native.Runtime.Space

%default covering

%cg native static Main.squares

squares : List Integer
squares = map (\i => i * i) [1 .. 3000]

main : IO ()
main = do
  setHeapLimit 65536   -- the copy under no limit sets none
  printLn (sum squares, length squares)
  collections <- collectionCount
  -- the list read again, after the collections the program made
  printLn (foldl (\acc, x => acc + x `div` 3) 0 squares, collections > 0)
