-- Foreign pointers, natively, are of two kinds, which the runtime tells
-- apart by the object a pointer is:
--
-- - an address of memory outside the heap, as `malloc` gives: what foreign
--   code could read, null or not, given back by `free`;
-- - a string of the heap, which the runtime gives where `base` asks it for
--   a pointer to zero-ended bytes and reads that pointer only through the
--   runtime. `getEnv`, `currentDir` and `getEnvironment` are such:
--
--       currentDir = do res <- primIO prim__currentDir
--                       if prim__nullPtr res /= 0 then pure Nothing
--                          else do let s = prim__getString res
--                                  free $ prim__forgetPtr res
--                                  pure (Just s)
--
--   `prim__getString` gives the string itself, no copy, and `free` does
--   nothing to it: the collector keeps it as long as anything holds it.
--
-- A program never holds a pointer of the second kind: `base`'s functions
-- that make them are its own. It sees each kind work, as the Chez backend
-- gives the same through the C library.
module Main

import Data.String
import System
import System.Directory
import System.FFI

main : IO ()
main = do
  p <- malloc 64
  putStrLn ("malloc 64 gives the null pointer: " ++ show (prim__nullAnyPtr p /= 0))
  free p
  q <- malloc 0
  free q
  -- many strings given as pointers, read and freed: none is kept
  for_ [1 .. 1000] $ \i => setEnv "IDR_PTR" (show i) True
  v <- getEnv "IDR_PTR"
  putStrLn ("getEnv after a thousand setEnv: " ++ show v)
  Just d <- currentDir
    | Nothing => putStrLn "no current directory"
  putStrLn ("currentDir ends with the test's directory: " ++ show (isSuffixOf "ptr001" d))
  env <- getEnvironment
  putStrLn ("getEnvironment has IDR_PTR: " ++ show (lookup "IDR_PTR" env))
