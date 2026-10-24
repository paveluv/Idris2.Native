-- A file's permissions changed, and what they then allow, printed: a file
-- made read-only cannot be opened for writing, and can again once its
-- permissions give the owner writing back; the permissions of a file that
-- is not there cannot be changed.
--
-- `chmod` takes a file's name and the permissions of its owner, its group
-- and everyone else, which `mkMode` makes the mode's bits of:
--
--     chmod "f" (MkPermissions [Read] [] [])          -- the mode 0o400
--     chmod "f" (MkPermissions [Read, Write] [Read] [Read])  -- 0o644
--
-- The system checks a file's permissions for every user but root, so the
-- read-only file refuses writing where the tests run as any other user;
-- under root both code generators open it alike.
module Main

import System.File

-- the file opened for writing, as whether it could be
canWrite : String -> IO String
canWrite name = do
  Right f <- openFile name Append
    | Left e => pure ("refused: " ++ show e)
  closeFile f
  pure "opened"

main : IO ()
main = do
  Right () <- writeFile "permissions.txt" "text\n"
    | Left e => putStrLn ("write: " ++ show e)
  r1 <- chmod "permissions.txt" (MkPermissions [Read] [] [])
  printLn (map (const ()) r1)
  putStrLn !(canWrite "permissions.txt")
  r2 <- chmod "permissions.txt" (MkPermissions [Read, Write] [Read] [Read])
  printLn (map (const ()) r2)
  putStrLn !(canWrite "permissions.txt")
  Right s <- readFile "permissions.txt"
    | Left e => putStrLn ("read: " ++ show e)
  printLn s
  r3 <- chmod "not-there.txt" (MkPermissions [Read] [] [])
  putStrLn (either (\e => "chmod: " ++ show e) (const "changed") r3)
  r4 <- chmodRaw "permissions.txt" 384
  printLn (map (const ()) r4)
  ignore (removeFile "permissions.txt")
