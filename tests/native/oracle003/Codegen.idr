-- Output that differs between code generators by design: the harness must
-- report it as a mismatch, which shows it compares at all.
module Main

import System.Info

main : IO ()
main = putStrLn ("running under " ++ codegen)
