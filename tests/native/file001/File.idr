-- Files written and read, natively: a file is an object of the heap, its
-- handle with what its reads found and its input buffer, which `base`
-- holds as a `FilePtr`. Writes go to the system as they are made; reads
-- take bytes from the buffer, 64 KiB, and ask the system again only when
-- it runs out, so the line longer than the buffer below grows it. The
-- Chez backend gives the same, through the C library's `FILE`.
--
-- In surface Idris, base's
--
--     fGetLine (FHandle f) = do res <- primIO (prim__readLine f)
--                               getStringAndFree (FHandle f) res
--
-- where the runtime gives the line, a string, as the pointer `base`
-- expects, which `getStringAndFree` reads, and frees, which for a string
-- of the heap does nothing. At the end, `fGetLine` gives the empty string
-- and `fEOF` turns true, as the C library's `getline` and `feof`.
module Main

import Data.String
import System
import System.File

-- Every line of the file, each shown, until its end.
lines' : File -> IO ()
lines' h = do
  Right l <- fGetLine h
    | Left e => putStrLn ("fGetLine: " ++ show e)
  eof <- fEOF h
  putStrLn ("line " ++ show l ++ (if eof then ", then the end" else ""))
  if eof then pure () else lines' h

main : IO ()
main = do
  Right () <- writeFile "out.txt" "line one\nline two\nété\nno newline"
    | Left e => putStrLn ("writeFile: " ++ show e)
  Right s <- readFile "out.txt"
    | Left e => putStrLn ("readFile: " ++ show e)
  putStrLn ("readFile: " ++ show s)
  Right h <- openFile "out.txt" Read
    | Left e => putStrLn ("openFile: " ++ show e)
  lines' h
  closeFile h
  -- bytes, a byte, a line passed over
  Right h <- openFile "out.txt" Read
    | Left e => putStrLn ("openFile: " ++ show e)
  Right cs <- fGetChars h 4
    | Left e => putStrLn ("fGetChars: " ++ show e)
  Right c <- fGetChar h
    | Left e => putStrLn ("fGetChar: " ++ show e)
  Right () <- fSeekLine h
    | Left e => putStrLn ("fSeekLine: " ++ show e)
  Right l <- fGetLine h
    | Left e => putStrLn ("fGetLine: " ++ show e)
  putStrLn ("fGetChars 4 " ++ show cs ++ ", fGetChar " ++ show c ++ ", after fSeekLine " ++ show l)
  Right size <- fileSize h
    | Left e => putStrLn ("fileSize: " ++ show e)
  putStrLn ("fileSize " ++ show size ++ ", isTTY " ++ show !(isTTY h))
  -- a write to a file opened to read fails, and says why
  r <- fPutStr h "no"
  putStrLn ("fPutStr to a file read: " ++ either show (const "written") r
            ++ ", fileError " ++ show !(fileError h))
  closeFile h
  -- appended, then a line longer than the buffer
  Right () <- appendFile "out.txt" "\nappended\n"
    | Left e => putStrLn ("appendFile: " ++ show e)
  Right h <- openFile "out.txt" Append
    | Left e => putStrLn ("openFile: " ++ show e)
  Right () <- fPutStrLn h (replicate 100000 'x')
    | Left e => putStrLn ("fPutStrLn: " ++ show e)
  Right () <- fPutStr h "last\n"
    | Left e => putStrLn ("fPutStr: " ++ show e)
  closeFile h
  Right s <- readFile "out.txt"
    | Left e => putStrLn ("readFile: " ++ show e)
  putStrLn ("lines " ++ show (map length (lines s)))
  -- what is not there
  r <- openFile "missing/out.txt" Read
  putStrLn ("openFile missing/out.txt: " ++ either show (const "opened") r)
  Right () <- removeFile "out.txt"
    | Left e => putStrLn ("removeFile: " ++ show e)
  r <- removeFile "out.txt"
  putStrLn ("removeFile twice: " ++ either show (const "removed") r)
  -- the standard files: the input's lines, then the output's and the errors'
  lines' stdin
  Right () <- fPutStrLn stdout "to stdout"
    | Left e => putStrLn ("fPutStrLn: " ++ show e)
  Right () <- fPutStrLn stderr "to stderr"
    | Left e => putStrLn ("fPutStrLn: " ++ show e)
  putStrLn "done"
