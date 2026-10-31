-- Lines read from the standard input natively: `getLine` gives the text
-- through the next newline, without it, or to the end of the input, and
-- the empty string once there is none, as the Chez backend does. A line
-- may be longer than the 64 KiB the runtime reads at a time; a carriage
-- return before the newline is part of the line's end, dropped with it,
-- as Chez and the C support drop it; text that is not ASCII comes through
-- as its UTF-8 bytes.
--
-- base reads it as `getLine = primIO prim__getStr`: the runtime's
-- `prim__getStr` reads from the standard input's buffer, which `readLine`
-- refills from the system when it holds no newline.
module Main

-- each line read, its length and its first and last characters; `getLine`
-- gives the empty string after the end, so reading on is no error
main : IO ()
main = traverse_ (\_ => do l <- getLine
                           putStrLn (show (length l) ++ " " ++ ends l))
                 [1 .. the Nat 9]
  where
    ends : String -> String
    ends s = case unpack s of
      [] => "(empty)"
      cs@(c :: _) => show (ord c) ++ ".." ++ show (ord (last' cs))
      where
        last' : List Char -> Char
        last' [x] = x
        last' (_ :: xs@(_ :: _)) = last' xs
        last' [] = ' '
