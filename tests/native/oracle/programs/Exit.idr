-- An exit status: the output, then exit with status 3.
module Main

import System

main : IO ()
main = do
  putStrLn "exiting with status 3"
  exitWith (ExitFailure 3)
