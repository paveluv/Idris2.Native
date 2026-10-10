-- Case analysis: on constructors of a user type, on Maybe and Either, and on
-- Int, Char and String constants.
module Main

data Shape = Circle Int | Rect Int Int | Triangle Int Int Int

perimeter : Shape -> Int
perimeter (Circle r) = 6 * r
perimeter (Rect w h) = 2 * (w + h)
perimeter (Triangle a b c) = a + b + c

describe : Maybe (Either Int String) -> String
describe Nothing = "nothing"
describe (Just (Left n)) = "number " ++ show n
describe (Just (Right s)) = "text " ++ s

digit : Int -> String
digit 0 = "zero"
digit 1 = "one"
digit 2 = "two"
digit _ = "many"

kind : Char -> String
kind 'a' = "vowel"
kind 'e' = "vowel"
kind ' ' = "space"
kind _ = "other"

greet : String -> String
greet "en" = "hello"
greet "fr" = "bonjour"
greet _ = "?"

main : IO ()
main = do
  printLn (map perimeter [Circle 2, Rect 3 4, Triangle 3 4 5])
  putStrLn (describe Nothing ++ ", " ++ describe (Just (Left 7)) ++ ", " ++ describe (Just (Right "x")))
  printLn (map digit [0, 1, 2, 3])
  printLn (map kind ['a', 'b', ' ', 'e'])
  printLn (map greet ["fr", "en", "de"])
