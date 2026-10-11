-- Closures: partial application, lambdas, higher-order functions and
-- function composition. A closure is an object holding a function's code
-- and the arguments given so far: `(+) 1` holds `(+)` and 1. Applying a
-- closure to one more argument either makes a new closure with it, or, when
-- that fills the function's arity, calls the code with them all.
module Main

adders : List (Int -> Int)
adders = map (+) [1, 2, 3]

twice : (a -> a) -> a -> a
twice f = f . f

scale : Int -> List Int -> List Int
scale k = map (* k)

main : IO ()
main = do
  printLn (map (\f => f 10) adders)
  printLn (foldr (\x, acc => x * 2 + acc) 0 [1 .. 10])
  printLn (filter (\x => mod x 3 == 0) [1 .. 20])
  printLn (twice (twice (+ 3)) 0)
  printLn (scale 5 [1, 2, 3])
