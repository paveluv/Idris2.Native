-- A file kept after it is closed, natively: `base` holds a file as an
-- `AnyPtr`, which the runtime makes a handle, a number of a slot of its
-- table of open files and of the times the slot has been taken. Closing a
-- file frees its slot; the next file opened takes it, under a new number.
-- So a use of the old file's `File` finds no file, and fails as of a bad
-- handle, where in C it would read whatever file took its place.
--
-- In surface Idris, base's
--
--     closeFile (FHandle f) = primIO (prim__close f)
--
-- where the runtime frees `f`'s slot; `fGetLine (FHandle f)` after it
-- answers `Left`, the reason the C library's `EBADF`.
module Main

import System.File

main : IO ()
main = do
  Right () <- writeFile "first.txt" "first\n"
    | Left e => putStrLn ("writeFile: " ++ show e)
  Right () <- writeFile "second.txt" "second\n"
    | Left e => putStrLn ("writeFile: " ++ show e)
  Right a <- openFile "first.txt" Read
    | Left e => putStrLn ("openFile: " ++ show e)
  closeFile a
  -- `b` takes the slot `a` had
  Right b <- openFile "second.txt" Read
    | Left e => putStrLn ("openFile: " ++ show e)
  r <- fGetLine a
  putStrLn ("the closed file: " ++ either show show r)
  r <- fGetLine b
  putStrLn ("the file opened after: " ++ either show show r)
  closeFile b
  ignore (removeFile "first.txt")
  ignore (removeFile "second.txt")
