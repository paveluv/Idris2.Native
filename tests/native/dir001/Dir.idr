-- The current directory, natively: `currentDir` asks the system for the
-- path of the current directory, and `changeDir` makes another the current
-- one, answering whether it could. The path goes to the system as its
-- bytes and a zero byte after them, copied out of the string for the call;
-- the answer comes back as such bytes, which `currentDir` copies into a new
-- string. The Chez backend gives the same, through the C library's `getcwd`
-- and `chdir`.
--
-- In surface Idris, base's
--
--     changeDir dir = do ok <- primIO (prim__changeDir dir)
--                        pure (ok == 0)
--
-- A relative path is from the current directory; `..` goes back up; a
-- non-ASCII name is its UTF-8 bytes; a directory that is not there leaves
-- the current one as it was.
module Main

import Data.List1
import Data.String
import System.Directory

-- the last part of the current directory's path, which does not depend on
-- where the test runs
here : IO String
here = do
  Just d <- currentDir
    | Nothing => pure "no current directory"
  pure (last (split (== '/') d))

step : String -> IO ()
step d = do
  ok <- changeDir d
  putStrLn (d ++ ": " ++ show ok ++ ", now in " ++ !here)

main : IO ()
main = do
  putStrLn ("in " ++ !here)
  traverse_ step ["sub", "été", "../..", "not-there", "/"]
  Just d <- currentDir
    | Nothing => putStrLn "no current directory"
  putStrLn d
