-- Ordinary code around the probe of `Probe.idr`, under a window of 8
-- bytes, where every allocation takes the slow path and the heap is
-- collected over and over. The margin past the limit must be committed
-- at start-up, after many allocations and collections, and after a
-- primitive's allocation of 256 KiB, which grows the heap in the middle of
-- the program's window. Each place prints whether it holds.
module Main

import Data.List
import Native.Flat.Uniform
import Probe

report : String -> Bits64 -> IO ()
report place ok = putStrLn (place ++ ": " ++ (if ok == 1 then "committed" else "NOT committed"))

main : IO ()
main = do
  report "at start-up" (marginHolds 0)
  -- a list of 10,000 cells, kept live across the collections its
  -- allocation makes
  let cells = [1 .. the Integer 10000]
  report "after many allocations" (marginHolds (cast (length cells)))
  let pieces = replicate 64 (pack (replicate 4096 'a'))
  report "after a primitive's allocation" (marginHoldsAfterJoin (MkUniform pieces))
  putStrLn ("cells: " ++ show (sum cells))
