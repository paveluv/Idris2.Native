||| A change to a file's text (`Edit`): what replaces the text between two
||| positions, which Idris's parser gives, and how a set of them is made.
|||
||| A refactoring (`Lint.Refactor.Refactoring`) plans edits at the positions
||| of the declarations and clauses it moves, and the rest of the file, its
||| layout and its comments, stays as written.
module Lint.Refactor.Edit

import Data.List
import Data.Maybe
import Data.String

%default total

||| The text between `from` and `to` (lines and columns from 0, as Idris
||| counts them; `to` excluded) replaced by `text`. An insertion has `from`
||| and `to` equal; a deletion has no text.
public export
record Edit where
  constructor MkEdit
  from : (Int, Int)
  to : (Int, Int)
  text : String

||| Lines inserted before the line `before`.
export
insertLines : (before : Int) -> List String -> Edit
insertLines before ls = MkEdit (before, 0) (before, 0) (fastConcat (map (++ "\n") ls))

||| The lines from `first` to `last`, both included, deleted.
export
deleteLines : (first, last : Int) -> Edit
deleteLines first last = MkEdit (first, 0) (last + 1, 0) ""

||| The lines from `first` to `last`, both included, replaced by others.
export
replaceLines : (first, last : Int) -> List String -> Edit
replaceLines first last ls = MkEdit (first, 0) (last + 1, 0) (fastConcat (map (++ "\n") ls))

||| The whole of a text replaced.
export
replaceAll : (old, new : String) -> Edit
replaceAll old new = MkEdit (0, 0) (cast (length (lines old)) + 1, 0) new

||| Where each line of a text starts, as an offset into it.
lineStarts : String -> List Nat
lineStarts t = 0 :: go 0 (unpack t)
  where
    go : Nat -> List Char -> List Nat
    go _ [] = []
    go i ('\n' :: cs) = S i :: go (S i) cs
    go i (_ :: cs) = go (S i) cs

||| The offset of a position in a text, a position past its end at its end.
offset : String -> List Nat -> (Int, Int) -> Nat
offset t starts (l, c) =
  case drop (cast l) starts of
    (s :: _) => min (length t) (s + cast c)
    [] => length t

||| The text with the edits made, or nothing if two of them overlap. Each
||| edit is placed by the positions of the text as given, so they are made
||| from the last to the first.
export
apply : List Edit -> String -> Maybe String
apply es t =
  let starts = lineStarts t
      spans = sortBy (\a, b => compare (fst b) (fst a)) (map (\e => (offset t starts e.from, offset t starts e.to, e.text)) es)
  in if overlapping spans then Nothing else Just (foldl replace t spans)
  where
    overlapping : List (Nat, Nat, String) -> Bool
    overlapping ((s, _, _) :: rest@((_, e', _) :: _)) = e' > s || overlapping rest
    overlapping _ = False

    replace : String -> (Nat, Nat, String) -> String
    replace acc (s, e, new) = substr 0 s acc ++ new ++ substr e (length acc `minus` e) acc

||| An edit as a reader checks it: where it is, the lines it removes from the
||| text, and those it puts there, a blank line as its mark alone.
export
describe : String -> Edit -> List String
describe t e =
  let starts = lineStarts t
      s = offset t starts e.from
      old = substr s (offset t starts e.to `minus` s) t
  in ("@@ line " ++ show (fst e.from + 1)) :: map (marked "-") (lines old) ++ map (marked "+") (lines e.text)
  where
    marked : String -> String -> String
    marked m l = if l == "" then m else m ++ " " ++ l

||| The edits that keep a text's layout under edits that change the length
||| of a line that opens a layout block after an edit (`do`, `of`, `let`,
||| `where`): each line after it indented past the edit's start, up to the
||| first that is not, hangs off what follows the edit (the rest of a `do`
||| block or of a `case` alternative), so it moves as far as the edits
||| before its indentation move the text. A line that opens no block after
||| its edits has no line hanging off it: what is indented under it is a
||| continuation, inside brackets or not, which may stay where it is. One
||| edit a line, its moves summed.
export
realigned : String -> List Edit -> List Edit
realigned t es =
  let ms = moves (lines t) in mapMaybe (moved ms) (nub (map fst ms))
  where
    growth : Edit -> Int
    growth e = cast (length e.text) - (snd e.to - snd e.from)

    -- the edits within a line that change its length: line, column, growth
    grown : List (Int, Int, Int)
    grown = [ (fst e.from, snd e.from, growth e) | e <- es, fst e.from == fst e.to, not (isInfixOf "\n" e.text), growth e /= 0 ]

    indentOf : String -> Int
    indentOf l = cast (length (takeWhile (== ' ') (unpack l)))

    -- the lines hanging off a line's edits, each with how far they move it
    hanging : List String -> List (Int, Int) -> Int -> List (Int, Int)
    hanging ls here l = go (l + 1) (drop (cast (l + 1)) ls)
      where
        start : Int
        start = foldr min (foldr max 0 (map fst here)) (map fst here)

        go : Int -> List String -> List (Int, Int)
        go _ [] = []
        go i (x :: xs) =
          if trim x == "" then go (i + 1) xs
          else if indentOf x <= start then []
          else (i, sum [ g | (c, g) <- here, c < indentOf x ]) :: go (i + 1) xs

    -- whether a line opens a layout block from a column on: a keyword of
    -- one among its words there
    opensBlock : String -> Int -> Bool
    opensBlock line c =
      let rest = drop (cast c) (unpack line)
          spaced = map (\ch => if isAlphaNum ch || ch == '_' || ch == '\'' then ch else ' ') rest
      in any (\w => w `elem` ["do", "of", "let", "where"]) (words (pack spaced))

    -- each line hanging off an edited one that opens a block after its
    -- first edit, with how far it moves
    moves : List String -> List (Int, Int)
    moves ls =
      concat [ hanging ls here l
             | l <- nub (map fst grown), let here = [ (c, g) | (l', c, g) <- grown, l' == l ]
             , opensBlock (fromMaybe "" (head' (drop (cast l) ls))) (foldr min 0x7FFFFFFF (map fst here)) ]

    -- a line's moves made one edit at its start
    moved : List (Int, Int) -> Int -> Maybe Edit
    moved ms i =
      let by = sum [ g | (i', g) <- ms, i' == i ] in
      if by > 0 then Just (MkEdit (i, 0) (i, 0) (pack (replicate (cast by) ' ')))
      else if by < 0 then Just (MkEdit (i, 0) (i, negate by) "")
      else Nothing
