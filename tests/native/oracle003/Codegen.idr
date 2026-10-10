-- Output that differs between code generators by design.
module Main

import System.Info

main : IO ()
main = putStrLn ("running under " ++ codegen)
