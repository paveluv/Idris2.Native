-- A negative array size, read as a word, does not fit the header.
import Data.IOArray

main : IO ()
main = do
  arr <- newArray {elem = Int} (-1)
  ignore (writeArray arr 0 1)
