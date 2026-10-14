||| The named arguments of an application as written (`namedArguments`):
||| `f {n = x} y`, or `f {n} y` for `{n = n}`.
|||
||| The parser keeps no place for a named argument's name, so a refactoring
||| that renames a function's implicit binder finds the names its calls give
||| it here, reading along the line from where the function is written.
module Lint.Refactor.NamedArguments

import Data.List
import Data.Maybe

%default covering

||| The named arguments `{name ...}` an application gives a function, from
||| where the function is written: where each name is, and whether it is
||| written short, `{n}` for `{n = n}`. The arguments are read along the
||| function's line, past the others, up to what ends the application: an
||| operator, a closing bracket, a keyword.
export
namedArguments : (text : List String) -> (at : (Int, Int)) -> (function, name : String) -> List ((Int, Int), Bool)
namedArguments ls (l, c) f n =
  let line = fromMaybe "" (head' (drop (cast l) ls))
      start = c + cast (length f)
  in go start (drop (cast start) (unpack line))
  where
    identChar : Char -> Bool
    identChar x = isAlphaNum x || x == '_' || x == '\'' || x == '.'

    -- the characters up to the bracket that closes one already open, and
    -- what follows it
    balanced : Nat -> List Char -> (Int, List Char)
    balanced Z cs = (0, cs)
    balanced _ [] = (0, [])
    balanced (S d) (x :: xs) =
      let depth = if x == '{' || x == '(' || x == '[' then S (S d) else if x == '}' || x == ')' || x == ']' then d else S d
          (k, rest) = balanced depth xs
      in (k + 1, rest)

    named : Int -> List Char -> List ((Int, Int), Bool)
    named i cs =
      let (sp, rest) = span (== ' ') cs
          (word, after) = span identChar rest
          j = i + cast (length sp)
      in if pack word /= n then [] else case dropWhile (== ' ') after of
           ('}' :: _) => [((l, j), True)]
           ('=' :: _) => [((l, j), False)]
           _ => []

    stops : List String
    stops = ["then", "else", "of", "in", "where", "with", "do", "let"]

    go : Int -> List Char -> List ((Int, Int), Bool)
    go i [] = []
    go i (' ' :: cs) = go (i + 1) cs
    go i ('{' :: cs) = let (k, more) = balanced 1 cs in named (i + 1) cs ++ go (i + 1 + k) more
    go i ('@' :: '{' :: cs) = let (k, more) = balanced 1 cs in go (i + 2 + k) more
    go i ('(' :: cs) = let (k, more) = balanced 1 cs in go (i + 1 + k) more
    go i ('[' :: cs) = let (k, more) = balanced 1 cs in go (i + 1 + k) more
    go i cs@(x :: _) =
      if identChar x
        then let (w, more) = span identChar cs in
             if pack w `elem` stops then [] else go (i + cast (length w)) more
        else []
