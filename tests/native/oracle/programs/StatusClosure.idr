-- Closures: partial application of known functions and of lambdas, folds,
-- composition, and a closure kept in a data structure.
--
-- `add3 1` is a closure of `add3` holding one argument, `partly 2` one
-- holding two, and `more 3` fills the arity and calls `add3`. The status is
-- 50 + 32 + 6 + 20 - 30 = 78.
module Main

import Data.So
import System

exitCode : Int -> IO ()
exitCode n = case choose (n == 0) of
  Left _ => exitSuccess
  Right _ => exitWith (ExitFailure n)

add3 : Int -> Int -> Int -> Int
add3 x y z = x + y + z

twice : (a -> a) -> a -> a
twice f = f . f

main : IO ()
main = do
  let xs = map (\x => x * 3 + 1) [1, 2, 3, 4, 5]
  let adders = map (+) [10, 20]
  let partly = add3 1
  let more = partly 2
  exitCode (foldl (+) 0 xs + foldr (\f, acc => f 1 + acc) 0 adders
            + more 3 + twice (twice (+ 5)) 0 - 30)
