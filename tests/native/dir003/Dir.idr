-- A directory's entries listed, natively: an open directory is a file the
-- runtime keeps, whose entries the system gives one at a time, each name
-- a string given as the pointer `base` expects. The Chez backend gives the
-- same, through the C library's `opendir` and `readdir`.
--
-- In surface Idris, base's
--
--     nextDirEntry (MkDir d) = do
--       res <- primIO (prim__dirEntry d)
--       if prim__nullPtr res /= 0
--         then if !getErrno /= 0 then returnError else pure (Right Nothing)
--         else ...
--
-- where the null pointer is the end when the last failure is 0: the
-- runtime clears it before each entry, as the C support clears `errno`.
-- `listDir` leaves out `.` and `..`; the order is the system's, so the
-- names are sorted to be shown.
module Main

import Data.List
import System
import System.Directory
import System.File

main : IO ()
main = do
  ignore $ createDir "listed"
  traverse_ (\n => ignore $ writeFile ("listed/" ++ n) n) ["b.txt", "a.txt", "été.txt"]
  ignore $ createDir "listed/sub"
  Right ns <- listDir "listed"
    | Left e => putStrLn ("listDir: " ++ show e)
  putStrLn ("listed: " ++ show (sort ns))
  Right d <- openDir "listed"
    | Left e => putStrLn ("openDir: " ++ show e)
  entries <- count d 0
  closeDir d
  putStrLn ("entries one by one: " ++ show entries)
  r <- listDir "missing"
  putStrLn ("listDir missing: " ++ either show show r)
  r <- listDir "listed/a.txt"
  putStrLn ("listDir of a file: " ++ either show show r)
  traverse_ (\n => ignore $ removeFile ("listed/" ++ n)) ["b.txt", "a.txt", "été.txt"]
  removeDir "listed/sub"
  removeDir "listed"
  putStrLn "done"
  where
    count : Directory -> Nat -> IO Nat
    count d n = do
      Right (Just _) <- nextDirEntry d
        | _ => pure n
      count d (S n)
