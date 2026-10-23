-- A file's times, printed: the modification and status-change times of a
-- file nothing writes while the program runs, its seconds and nanoseconds,
-- and of its access time only whether there is one, since reading a file
-- may change it.
--
-- `fileTime` asks the system for the open file's three times, each
-- seconds since the epoch and the nanoseconds past them:
--
--     Right t <- fileTime f
--     printLn t.mtime.sec
--
-- In the C library it is `fstat`, its answer copied into a structure that
-- base reads field by field and then frees; natively the runtime makes
-- the same structure, of six words, from the system's answer.
module Main

import System.File

main : IO ()
main = do
  Right f <- openFile "/etc/passwd" Read
    | Left e => putStrLn ("open: " ++ show e)
  Right t <- fileTime f
    | Left e => putStrLn ("fileTime: " ++ show e)
  printLn (t.mtime.sec, t.mtime.nsec)
  printLn (t.ctime.sec, t.ctime.nsec)
  printLn (t.atime.sec > 0, t.atime.nsec >= 0 && t.atime.nsec < 1000000000)
  Right m <- fileModifiedTime f
    | Left e => putStrLn ("fileModifiedTime: " ++ show e)
  printLn (m == t.mtime.sec)
  closeFile f
