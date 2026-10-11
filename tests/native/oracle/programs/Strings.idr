-- String primitives that allocate: unpack, pack, append, substrings,
-- conversions and long strings. A string is an object of its bytes on the
-- heap, its length in its header.
module Main

import Data.String

main : IO ()
main = do
  let s = "The quick brown fox jumps over the lazy dog"
  putStrLn (pack (reverse (unpack s)))
  printLn (length s)
  putStrLn (substr 4 5 s)
  putStrLn (concat (replicate 3 "ab"))
  putStrLn (unwords (map show [the Int 1 .. 12]))
  let long = concatMap show [the Int 1 .. 2000]
  printLn (length long)
  putStrLn (substr 1000 30 long)
  printLn (words s)
  putStrLn (toUpper s)
