||| The constraints of a type as written (`constraintsOf`): each argument of
||| an arrow `C x =>`, which search fills, as its text in the file; and a
||| claim's text with one of them taken out (`withoutConstraint`).
|||
||| A function moved into the scope of one with the same constraint needs
||| it no more: search finds the enclosing one, so the moved function's own
||| is a second parameter of the same meaning.
module Lint.Refactor.Constraints

import Lint.Refactor.Span

import Core.TT
import Core.TT.Binder
import Data.List
import Data.String
import Idris.Syntax

%default covering

||| The text of the file between two places, a line and a column each, the
||| end past its last character.
textBetween : List String -> (from, to : (Int, Int)) -> String
textBetween ls (sl, sc) (el, ec) =
  let inside = take (cast (el - sl + 1)) (drop (cast sl) ls) in
  case inside of
    [] => ""
    [one] => substr (cast sc) (cast (ec - sc)) one
    (first :: rest) =>
      joinBy "\n" (substr (cast sc) (length first) first :: (take (length rest `minus` 1) rest
                   ++ maybe [] (\l => [substr 0 (cast ec) l]) (last' rest)))

||| A text with its spaces made single, to compare two as written.
export
tidy : String -> String
tidy = unwords . words

||| A term as written in the file's lines, if it has a place.
export
writtenAs : (text : List String) -> PTerm -> List String
writtenAs ls t = case Span.bounds (getPTermLoc t) of
  Just (s, e) => [textBetween ls s e]
  Nothing => []

||| The constraints of a type, each as written in the file's lines: the
||| arguments of its arrows `C x =>`, from the outside in.
export
constraintsOf : (text : List String) -> PTerm -> List String
constraintsOf ls (PPi _ _ AutoImplicit Nothing a r) = writtenAs ls a ++ constraintsOf ls r
constraintsOf ls (PPi _ _ _ _ _ r) = constraintsOf ls r
constraintsOf _ _ = []

||| A text without the constraint written as given, its `=>` and the spaces
||| and line breaks after it, at the constraint's first place: the type goes
||| on where the constraint was.
export
withoutConstraint : (written : String) -> String -> String
withoutConstraint w t = go [] (unpack t)
  where
    ws : List Char
    ws = unpack w

    -- the arrow after the constraint, and what follows it
    arrow : List Char -> Maybe (List Char)
    arrow cs = case dropWhile (== ' ') cs of
      ('=' :: '>' :: rest) => Just (dropWhile (\c => c == ' ' || c == '\n') rest)
      _ => Nothing

    go : List Char -> List Char -> String
    go acc [] = pack (reverse acc)
    go acc cs@(c :: more) =
      if isPrefixOf ws cs
         then case arrow (drop (length ws) cs) of
                Just rest => pack (reverse acc) ++ pack rest
                Nothing => go (c :: acc) more
         else go (c :: acc) more
