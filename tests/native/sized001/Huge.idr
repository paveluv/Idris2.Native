-- An array of 2^60 elements does not fit the header's 56 bits.
import Data.IOArray

main : IO ()
main = do
  arr <- newArray {elem = Int} 1152921504606846976
  ignore (writeArray arr 0 1)
