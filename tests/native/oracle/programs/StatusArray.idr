-- Arrays through Data.IOArray, reporting through the exit status: a small
-- array, written inside and outside its bounds, and one of 200 elements,
-- larger than a small allocation window, filled and summed by loops. The
-- elements nobody wrote are the fill, Nothing, read here as 100.
--
-- An array is an object of its elements, uniform values, its number in its
-- header. The small array sums to 100 + 7 + 100, the write at index 3 is
-- refused, and the large one sums to 594, so the status is
-- (207 + 594 + 1) mod 256 = 34.
module Main

import Data.IOArray
import Data.Maybe
import Data.So
import System

exitCode : Int -> IO ()
exitCode n = case choose (n == 0) of
  Left _ => exitSuccess
  Right _ => exitWith (ExitFailure n)

fill : IOArray Int -> Int -> IO ()
fill arr i =
  if i >= max arr then pure ()
  else do ignore (writeArray arr i (i `mod` 7))
          fill arr (i + 1)

sumFrom : IOArray Int -> Int -> Int -> IO Int
sumFrom arr i acc =
  if i >= max arr then pure acc
  else do v <- readArray arr i
          sumFrom arr (i + 1) (acc + fromMaybe 100 v)

main : IO ()
main = do
  small <- newArray 3
  ok <- writeArray small 1 7
  outside <- writeArray small 3 9
  a <- sumFrom small 0 0
  big <- newArray 200
  fill big 0
  b <- sumFrom big 0 0
  exitCode ((a + b + (if ok then 1 else 0) + (if outside then 2 else 0)) `mod` 256)
