-- The smallest program with output. Under the native backend it reaches
-- the abort stub, since output is not lowered yet.
module Main

main : IO ()
main = putStrLn "hello, world"
