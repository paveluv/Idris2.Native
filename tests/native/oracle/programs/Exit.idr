-- An exit status: the output, then exit with status 3. The native backend
-- lowers the exit, but not the output before it.
module Main

import System

main : IO ()
main = do
  putStrLn "exiting with status 3"
  exitWith (ExitFailure 3)
