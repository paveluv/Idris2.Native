-- Changing the program's environment, natively: `setEnv` sets a variable,
-- or keeps its value when told not to overwrite it; `unsetEnv` removes it;
-- `getEnvironment` lists every entry, in order. The first change makes the
-- environment the runtime's own: the system's entries are copied into an
-- array of the runtime's, outside the heap, and a variable set is a new
-- entry, `NAME=value`, there. Names that cannot be a variable's, empty or
-- with `=` in them, are refused, as the C library refuses them. Many
-- variables set in a row make the array grow. Removing a variable moves
-- the last entry into its place, so the list is in the order the entries
-- were made, but for that. The Chez backend, which calls the C library,
-- gives the same, but for the variables its launcher adds to the
-- environment (`LD_LIBRARY_PATH`, `PWD`, ...), which it lists too.
module Main

import Data.List
import System

show' : String -> IO ()
show' n = putStrLn (n ++ ": " ++ show !(getEnv n))

many : Nat -> IO ()
many Z = pure ()
many (S k) = do
  ignore (setEnv ("IDR_MANY_" ++ show k) (show (k * k)) True)
  many k

main : IO ()
main = do
  show' "IDR"
  printLn !(setEnv "IDR_NEW" "fresh" True)
  show' "IDR_NEW"
  printLn !(setEnv "IDR" "replaced" True)
  show' "IDR"
  printLn !(setEnv "IDR" "kept?" False)
  show' "IDR"
  printLn !(setEnv "" "empty name" True)
  printLn !(setEnv "A=B" "a name with =" True)
  printLn !(unsetEnv "IDR_KEEP")
  show' "IDR_KEEP"
  printLn !(unsetEnv "IDR_NONE")
  many 40
  show' "IDR_MANY_0"
  show' "IDR_MANY_39"
  env <- getEnvironment
  putStrLn (show (length env) ++ " entries")
  traverse_ (\(k, v) => putStrLn (k ++ "=" ++ v)) (take 5 env)
