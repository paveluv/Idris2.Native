-- The compiler's own string iterator (`Libraries.Data.String.Iterator`),
-- which its lexer walks source text with, on both code generators. The two
-- print the same, so the expected output holds the same lines twice.
--
-- An iterator is a position in a string, which `uncons` takes one
-- character further:
--
--     withString str $ \it => case uncons str it of
--       EOF => ...                          -- nothing left
--       Character c it' => ...              -- c, then the rest from it'
--
-- and `withIteratorString` gives the string from a position on. Chez's
-- position is a character's index; the native one is the string encoding's
-- own, a byte offset into UTF-8, so a step is a character's bytes, one to
-- four, and no step counts the characters before it.
module Main

import Libraries.Data.String.Iterator

-- the characters of a string, by the iterator
chars : String -> List Char
chars str = withString str (go [])
  where
    go : List Char -> (1 it : StringIterator str) -> List Char
    go acc it = case uncons str it of
      EOF => reverse acc
      Character c it' => go (c :: acc) (assert_smaller it it')

-- the first word of a string, and the rest after its space, as a lexer
-- takes a token and goes on from where it ends
word : String -> (String, String)
word str = withString str (go [])
  where
    go : List Char -> (1 it : StringIterator str) -> (String, String)
    go acc it = case uncons str it of
      EOF => (pack (reverse acc), "")
      Character ' ' it' => withIteratorString str it' (\rest => (pack (reverse acc), rest))
      Character c it' => go (c :: acc) (assert_smaller it it')

samples : List String
samples = ["", "a", "héllo", "€uro", "\x1F600 smile", "ascii only", "日本 語"]

main : IO ()
main = do
  traverse_ (\s => printLn (chars s)) samples
  traverse_ (\s => printLn (word s)) samples
  printLn (Libraries.Data.String.Iterator.foldl (\n, c => n + ord c) 0 "h\x1F600é€")
