-- Integer and Nat arithmetic within the fixnum range, and comparisons. A
-- `Nat` is an `Integer` at run time, so `len` counts in fixnums. The status
-- is (338350 + 10 + 1) mod 256 = 185.
module Main

import Data.So
import System

exitCode : Int -> IO ()
exitCode n = case choose (n == 0) of
  Left _ => exitSuccess
  Right _ => exitWith (ExitFailure n)

sumSquares : Integer -> Integer -> Integer
sumSquares 0 acc = acc
sumSquares n acc = sumSquares (n - 1) (acc + n * n)

len : List a -> Nat
len [] = Z
len (_ :: xs) = S (len xs)

main : IO ()
main = exitCode (cast (sumSquares 100 0)
                 + cast (len [1, 2, 3, 4, 5, 6, 7] + 3)
                 + (if the Integer 3000000000 * 2 > 5999999999 then 1 else 0))
