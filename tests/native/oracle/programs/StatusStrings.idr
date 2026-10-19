-- Strings: literals, the eight primitives, comparison, and the lists of
-- characters and of strings, on ASCII and on other text, with values known
-- only at run time (`str` is not inlined, so nothing folds the operations).
-- The exit status is the number of checks that fail.
--
-- Under the native backend a string is UTF-8 with a bit in its header that
-- says every byte is ASCII. With the bit, a character is a byte, and
-- `length`, `strIndex` and `substr` are byte operations; without it they
-- scan. Each check below runs on text of both kinds: "héllo" has a
-- two-byte character, "日本" three-byte ones, and "𝄞" a four-byte one. A
-- string an operation makes knows its bit without another pass: `++` is
-- ASCII when both sides are, a part of an ASCII string is ASCII, and a part
-- of other text is ASCII when the bytes copied are.
module Main

import Data.So
import Data.String
import System

exitCode : Int -> IO ()
exitCode n = case choose (n == 0) of
  Left _ => exitSuccess
  Right _ => exitWith (ExitFailure n)

%noinline
str : String -> String
str x = x

failed : Bool -> Int
failed True = 0
failed False = 1

-- partial: the primitives for head, tail and index have no value past the
-- end of the string
partial
checks : List Bool
checks =
  [ length (str "hello") == 5, length (str "héllo") == 5, length (str "日本") == 2
  , length (str "𝄞x") == 2, length (str "") == 0
  , strIndex (str "hello") 1 == 'e', strIndex (str "héllo") 1 == 'é',
    strIndex (str "héllo") 2 == 'l'
  , strIndex (str "日本") 1 == '本', strIndex (str "𝄞x") 0 == '𝄞'
  , prim__strHead (str "héllo") == 'h', prim__strHead (str "日本") == '日'
  , prim__strTail (str "héllo") == "éllo", prim__strTail (str "𝄞x") == "x",
    prim__strTail (str "a") == ""
  , strCons 'x' (str "yz") == "xyz", strCons 'é' (str "t") == "ét", strCons '𝄞' (str "") == "𝄞"
  , str "ab" ++ str "cd" == "abcd", str "hé" ++ str "llo" == "héllo", str "" ++ str "" == ""
  , reverse (str "hello") == "olleh", reverse (str "héllo") == "olléh", reverse (str "日本𝄞") == "𝄞本日"
  , substr 1 3 (str "hello") == "ell", substr 1 3 (str "héllo") == "éll",
    substr 0 1 (str "日本") == "日"
  , substr 3 10 (str "hello") == "lo", substr 9 2 (str "hello") == "",
    substr 5 1 (str "hello") == ""
  , prim__strSubstr (-2) 3 (str "hello") == "hel", prim__strSubstr 1 (-1) (str "hello") == ""
  , str "abc" < str "abd", str "ab" < str "abc", not (str "b" < str "abc"), str "z" < str "é"
  , str "é" < str "日", str "日" < str "𝄞", str "same" == str "same", str "héllo" /= str "hello"
  , compare (str "x") (str "x") == EQ, str "b" >= str "a", str "a" <= str "a", str "b" > str "a"
  , pack (unpack (str "héllo")) == "héllo", length (unpack (str "日本𝄞")) == 3
  , unpack (str "hé") == ['h', 'é'], pack ['𝄞', 'a'] == "𝄞a", pack [] == ""
  , fastConcat [str "a", str "é", str "", str "日"] == "aé日", concat [str "x", str "y"] == "xy"
  , fastConcat [] == "", length (fastConcat (replicate 300 (str "ab"))) == 600
  , isPrefixOf "hé" (str "héllo"), words (str " a  b ") == ["a", "b"]
  ]

partial
main : IO ()
main = exitCode (sum (map failed checks))
