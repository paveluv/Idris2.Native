-- An array of 2^60 elements does not fit the header's 56 bits. Every heap
-- object starts with a header word, which says what the object is and how
-- big; an array's holds its number of elements in 56 bits. The count is
-- checked before allocating, so the program ends with a message instead of
-- making an object smaller than its header claims.
import Data.IOArray

main : IO ()
main = do
  arr <- newArray {elem = Int} 1152921504606846976
  ignore (writeArray arr 0 1)
