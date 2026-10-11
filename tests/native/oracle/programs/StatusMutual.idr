-- Three million mutual tail calls: real tail calls run them in constant
-- space, while a call stack would need far more than the usual 8 MiB. The
-- status is (2 + 4 + 3000000) mod 256 = 198.
module Main

import Data.So
import System

exitCode : Int -> IO ()
exitCode n = case choose (n == 0) of
  Left _ => exitSuccess
  Right _ => exitWith (ExitFailure n)

mutual
  isEven : Int -> Bool
  isEven 0 = True
  isEven n = isOdd (n - 1)

  isOdd : Int -> Bool
  isOdd 0 = False
  isOdd n = isEven (n - 1)

loop : Int -> Int -> Int
loop 0 acc = acc
loop n acc = loop (n - 1) (acc + 3)

main : IO ()
main = exitCode ((if isEven 3000001 then 1 else 2) + (if isOdd 2999999 then 4 else 8) + loop 1000000 0)
