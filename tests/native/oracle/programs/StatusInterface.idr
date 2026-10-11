-- Interfaces passed as dictionaries: a user interface with a default
-- method, instances for a base type and for lists, and Eq and Ord on a user
-- data type.
--
-- `weigh` at `List Int` is given the dictionary of `Weigh Int` to build the
-- list's, and `heavy`, a default method, calls `weigh` through the
-- dictionary it is in. The status is 6 + 40 + 7 + 11 = 64.
module Main

import Data.So
import System

exitCode : Int -> IO ()
exitCode n = case choose (n == 0) of
  Left _ => exitSuccess
  Right _ => exitWith (ExitFailure n)

interface Weigh a where
  weigh : a -> Int
  heavy : a -> Int
  heavy x = weigh x * 10

Weigh Int where
  weigh n = n

Weigh a => Weigh (List a) where
  weigh xs = foldl (\acc, x => acc + weigh x) 0 xs

data Colour = Red | Green | Blue

Eq Colour where
  Red == Red = True
  Green == Green = True
  Blue == Blue = True
  _ == _ = False

main : IO ()
main = exitCode (weigh (the (List Int) [1, 2, 3]) + heavy (the Int 4)
                 + (if Red == Red && Green /= Blue then 7 else 0)
                 + (if compare (the Int 3) 5 == LT then 11 else 0))
