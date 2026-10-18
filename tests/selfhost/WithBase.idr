||| The ladder's third module to check: one importing base, so checking it
||| reads base's TTCs, which the Prelude's do not bring.
module WithBase

import Data.SortedMap
import Data.String
import System.File

%default total

counts : List String -> SortedMap String Nat
counts = foldl (\m, w => insert w (maybe 1 S (lookup w m)) m) empty

-- `readFile` reads to the end of the file by fuel without end, which is
-- not total
covering
main : IO ()
main = do
  Right text <- readFile "WithBase.idr"
    | Left err => printLn err
  printLn (length (lines text), take 3 (SortedMap.toList (counts (words text))))
