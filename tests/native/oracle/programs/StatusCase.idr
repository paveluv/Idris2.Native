-- Case analysis on user data types, Maybe and Either, and on Int and Char
-- constants; constructors with and without fields.
module Main

import Data.So
import System

exitCode : Int -> IO ()
exitCode n = case choose (n == 0) of
  Left _ => exitSuccess
  Right _ => exitWith (ExitFailure n)

data Shape = Circle Int | Rect Int Int | Triangle Int Int Int | Empty

perimeter : Shape -> Int
perimeter (Circle r) = 6 * r
perimeter (Rect w h) = 2 * (w + h)
perimeter (Triangle a b c) = a + b + c
perimeter Empty = 0

score : Maybe (Either Int Int) -> Int
score Nothing = 1
score (Just (Left n)) = n
score (Just (Right n)) = 2 * n

digit : Int -> Int
digit 0 = 10
digit 1 = 20
digit _ = 30

vowel : Char -> Int
vowel 'a' = 1
vowel 'e' = 1
vowel _ = 0

main : IO ()
main = exitCode (sum (map perimeter [Circle 2, Rect 3 4, Triangle 3 4 5, Empty])
                 + score Nothing + score (Just (Left 7)) + score (Just (Right 4))
                 + digit 0 + digit 2 + vowel 'a' + vowel 'z')
