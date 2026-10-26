-- Tables `tabulate` refuses to make, which a read could load past: one of
-- more words than an `Int` counts, which counted as an `Int` would wrap
-- around to none, and one of rows of no words. The program ends where it
-- would make one, in `tabulate`: natively at an unmarked table's first
-- read. Each is read only when the program is given its name, so that a
-- run ends at the one it names. (Chez makes its constants before `main`,
-- so that a run of it would end at the first, whatever it is given.)
module Main

import Native.Support.Table
import Native.Support.Table.Row
import System

%default covering

-- Every `Int` from the least to the greatest: 2^64 words, which an `Int`
-- counts as 0.
everyInt : Table (-9223372036854775807 - 1) 9223372036854775807 Bits64
everyInt = tabulate (\k => cast k)

-- A row type of no words: a word, which no table holds.
record Wordless where
  constructor MkWordless
  value : Bits64

%inline
Row Wordless where
  rowWords = 0
  word x _ = x.value
  row w = MkWordless (w 0)

-- Ten rows of no words.
wordless : Table 0 9 Wordless
wordless = tabulate (\k => MkWordless (cast k))

main : IO ()
main = do
  [_, which] <- getArgs
    | _ => putStrLn "the name of a table, please"
  putStrLn ("reading " ++ which)
  case which of
    "everyInt" => printLn (Table.index everyInt 0 Refl)
    "wordless" => printLn ((Table.index wordless 0 Refl).value)
    _ => putStrLn "no such table"
