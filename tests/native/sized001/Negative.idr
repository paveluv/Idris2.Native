-- A negative array size, read as a word, does not fit the header: -1 is
-- the word 2^64 - 1, far beyond its 56 bits.
import Data.IOArray

main : IO ()
main = do
  arr <- newArray {elem = Int} (-1)
  ignore (writeArray arr 0 1)
