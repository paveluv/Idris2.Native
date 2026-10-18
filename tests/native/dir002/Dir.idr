-- Directories made and removed, natively, and why a service failed: each
-- OS service that fails records the reason as the runtime's last failure,
-- one of the reasons every platform tells apart (`Native.Failure`), and the
-- runtime gives `base` the C library's error number for it, which
-- `getErrno` answers and the file errors are read from. The Chez backend
-- gives the same, through the C library's `mkdir`, `rmdir` and `errno`.
--
-- In surface Idris, base's
--
--     createDir dir = do res <- primIO (prim__createDir dir)
--                        if res == 0 then ok () else returnError
--
-- where `returnError` turns the last failure into a `FileError`:
-- `FileExists` for a directory made twice, `FileNotFound` under a
-- directory that is not there. `removeDir` answers nothing: whether it
-- removed the directory shows in what follows, and why not in `getErrno`.
-- A service that succeeds leaves the last failure as it was, as the C
-- library leaves `errno`: after `new` is removed, `getErrno` still gives
-- the `ENOENT` (2) of `missing/new`; `full` has a file in it (`ENOTEMPTY`,
-- 39).
module Main

import System
import System.Directory
import System.Errno

made : String -> IO ()
made d = putStrLn ("createDir " ++ d ++ ": " ++ either show (const "made") !(createDir d))

removed : String -> IO ()
removed d = do
  removeDir d
  putStrLn ("removeDir " ++ d ++ ", then errno " ++ show !getErrno)

main : IO ()
main = do
  made "new"
  made "new"
  made "missing/new"
  made "été"
  removed "new"
  made "new"
  removed "full"
  removed "not-there"
  ok <- changeDir "not-there"
  putStrLn ("changeDir not-there: " ++ show ok ++ ", errno " ++ show !getErrno)
  removed "new"
  removed "été"
