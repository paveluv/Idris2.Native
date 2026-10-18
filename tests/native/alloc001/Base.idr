-- base's `malloc` and `free` (`System.FFI`), natively: blocks of many
-- sizes, small ones in slabs and some of 200 KB as chunks of their own,
-- given back in part, allocated again and given back all. `malloc` gives a
-- pointer, the null one when there is no memory; the program counts the
-- null ones, and none is. A pointer is an `AnyPtr`, which ordinary code
-- holds as an object of its address.
module Main

import Data.List
import System.FFI

sizes : List Int
sizes = [ (i * 37) `mod` 3000 + (if i `mod` 17 == 0 then 200000 else 1) | i <- [1 .. 400] ]

nulls : List AnyPtr -> Nat
nulls ps = length (filter (\p => prim__nullAnyPtr p /= 0) ps)

main : IO ()
main = do
  ps <- traverse malloc sizes
  putStrLn ("blocks: " ++ show (length ps) ++ ", null: " ++ show (nulls ps))
  traverse_ free (take 300 ps)
  qs <- traverse malloc (take 300 sizes)
  putStrLn ("again: " ++ show (length qs) ++ ", null: " ++ show (nulls qs))
  traverse_ free (drop 300 ps ++ qs)
