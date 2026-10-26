-- Constants marked static whose values the prelude's functions between
-- strings and lists compute: `pack`, `unpack`, `unlines`, `show` of a
-- string and `fastConcat`. Natively the runtime's string module computes
-- those functions as the program runs; the code generator computes them
-- as the runtime would, as it compiles the program, and the image holds
-- the value: a string as a literal's object, a list of characters as its
-- cells, each head the fixnum of a character. It is as if the program
-- had been written
--
--   packed = "caf\233 \8364\128512"
--   unpacked = ['h', '\233', 'l', 'l', 'o']
--
-- Idris's characters and strings hold Unicode scalar values only, and a
-- string's object holds their UTF-8, its header the count of its bytes
-- and whether all of them are ASCII, so a string of characters beyond
-- ASCII, which take two, three and four bytes, is counted in characters
-- (`length`) as the one the program makes.
--
-- Each is compared with the same value made as the program runs, and
-- every code generator prints the same, so the expected output holds the
-- same lines three times: native, Chez, and native under the encoding
-- whose pointers carry a tag.
module Main

import Data.String
import System

%default covering

%cg native static Main.packed Main.unpacked Main.joined Main.escaped Main.empties

-- `pack`, which Idris compiles as the prelude's `fastPack`: the string of
-- these seven characters, of 1, 2, 3 and 4 bytes, thirteen in all.
packed : String
packed = pack ['c', 'a', 'f', '\233', ' ', '\8364', '\128512']

-- `unpack`, the prelude's `fastUnpack`: the list of the characters of a
-- string beyond ASCII, as if written
--
--   unpacked = <the cell 104 :: <the cell 233 :: ... :: Nil>>
--
-- five cells, each of the fixnum of a character and the address of the
-- next, the last's the object every `Nil` is.
unpacked : List Char
unpacked = unpack "h\233llo"

-- `unlines`, which is `fastConcat` of the lines each followed by "\n":
-- as if written `joined = "static\ncaf\233\n\n"`.
joined : String
joined = unlines ["static", "caf\233", ""]

-- `show` of a string, which unpacks it and escapes what a literal
-- escapes: a tab, the quotes, a character beyond ASCII by its number,
-- with "\&" before the digit after it, control characters by their names,
-- with "\&" between "\SO" and an "H", the backslash and DEL. As if written
--
--   escaped = "\"a\\tb \\\"q\\\" caf\\233\\&9 \\SOH\\SO\\&H \\\\ \\DEL\""
escaped : String
escaped = show ("a\tb \"q\" caf\233" ++ "9 \SOH\SO" ++ "H \\ \DEL")

-- Each function at nothing: the empty string, the empty list and the
-- empty string, as if written `empties = ("", [], "")`.
empties : (String, List Char, String)
empties = (pack [], unpack "", fastConcat [])

-- Reads of the constants, by which the test finds them in the image:
-- each returns its value, a string's object or the first cell, as if
-- written
--
--   packedFrom _ = <the address of the string "caf\233 \8364\128512">
packedFrom : Int -> String
packedFrom _ = packed

unpackedFrom : Int -> List Char
unpackedFrom _ = unpacked

main : IO ()
main = do
  -- 1, which only the running program knows, so that what is made from
  -- it below is made as the program runs, by the runtime's functions
  n <- pure (length !getArgs)
  let e = chr (232 + cast n)
  let made = pack ['c', 'a', 'f', e, ' ', chr (8363 + cast n), chr (128511 + cast n)]
  printLn (packedFrom 0, packedFrom 0 == made)
  printLn (length (packedFrom 0), length made)
  printLn (unpackedFrom 0, unpackedFrom 0 == unpack ("h" ++ cast e ++ "llo"))
  printLn (joined, joined == unlines ["static", "caf" ++ cast e, ""])
  putStrLn escaped
  printLn (escaped == show ("a\tb \"q\" caf" ++ cast e ++ "9 \SOH\SO" ++ "H \\ \DEL"))
  let none = minus n 1
  printLn (empties,
           empties == (pack (replicate none 'x'), unpack (pack (replicate none 'x')),
                       fastConcat (replicate none "x")))
