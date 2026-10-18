-- The program's arguments, natively: `getArgs` gives the program's name
-- first, as the system put it at the stack pointer of the program's entry,
-- then each argument's bytes, a non-ASCII one and an empty one included.
-- Each is copied from the memory the system gave into a new string. The
-- name is the path the program was run by, which differs between code
-- generators (Chez's is its launcher's), so this prints only that there is
-- one, and the rest.
module Main

import System

main : IO ()
main = do
  args <- getArgs
  putStrLn (show (length args) ++ " arguments")
  case args of
    [] => putStrLn "no name"
    (_ :: rest) => traverse_ (\a => putStrLn ("[" ++ a ++ "] " ++ show (length a))) rest
