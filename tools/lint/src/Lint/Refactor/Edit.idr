||| A change to a file's text (`Edit`): what replaces the text between two
||| positions, which Idris's parser gives, and how a set of them is made.
|||
||| A refactoring (`Lint.Refactor.Refactoring`) plans edits at the positions
||| of the declarations and clauses it moves, and the rest of the file, its
||| layout and its comments, stays as written.
module Lint.Refactor.Edit

import Data.List
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
