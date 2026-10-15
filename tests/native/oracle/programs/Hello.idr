-- The smallest program with output: its `putStrLn` is the prelude's
-- foreign `prim__putStr`, which the runtime implements.
module Main

main : IO ()
main = putStrLn "hello, world"
