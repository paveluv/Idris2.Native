||| Binders as written (`binderGroups`): the bracketed groups of a type or of
||| a `parameters` block's header, each as written and with its spaces made
||| single, and what an auto-implicit one binds.
module Lint.Refactor.Binders

import Data.List
import Data.String

%default covering

||| The bracketed groups of a text, `{...}` and `(...)`, at the outer depth:
||| each as written and with its spaces made single. A group may run over
||| lines.
export
binderGroups : String -> List (String, String)
binderGroups t = go Z [] [] (unpack t)
  where
    tidy : List Char -> String
    tidy cs = unwords (words (pack cs))

    -- depth, the group so far (backwards), the groups so far (backwards)
    go : Nat -> List Char -> List (String, String) -> List Char -> List (String, String)
    go _ _ done [] = reverse done
    go Z _ done (c :: cs) =
      if c == '{' || c == '(' then go 1 [c] done cs else go Z [] done cs
    go (S d) cur done (c :: cs) =
      let cur' = c :: cur in
      if c == '{' || c == '(' then go (S (S d)) cur' done cs
      else if c == '}' || c == ')' then
        (case d of
           Z => go Z [] ((pack (reverse cur'), tidy (reverse cur')) :: done) cs
           _ => go d cur' done cs)
      else go (S d) cur' done cs

||| What an auto-implicit group binds, `{auto c : T}` or `{auto 0 c : T}`:
||| its name and its type, with spaces made single.
export
autoBinder : (tidy : String) -> Maybe (String, String)
autoBinder g =
  case words (substr 1 (length g `minus` 2) g) of
    ("auto" :: rest) => case dropWhile (\w => w == "0" || w == "1") rest of
      (n :: ":" :: ty) => Just (n, unwords ty)
      _ => Nothing
    _ => Nothing

||| A claim's first line with a type's start put before its type, after the
||| claim's `:`: `name : forall a . {p : P} -> type`.
export
prefixType : (start : String) -> (claimLine : String) -> String
prefixType start l =
  let (names, rest) = break (== ':') l in
  case strUncons rest of
    Just (':', ty) => names ++ ": " ++ start ++ ltrim ty
    _ => l

||| A type's text without a binder group as written, and the arrow after it
||| with the spaces and line breaks after that: the type goes on where the
||| group was, `f : FlatProblem -> ...` and not `f : ` over a line of its own.
export
withoutBinder : (group : String) -> String -> String
withoutBinder g t = go [] (unpack t)
  where
    gs : List Char
    gs = unpack g

    arrow : List Char -> List Char
    arrow cs = case dropWhile (== ' ') cs of
      ('-' :: '>' :: rest) => dropWhile (\c => c == ' ' || c == '\n') rest
      _ => cs

    go : List Char -> List Char -> String
    go acc [] = pack (reverse acc)
    go acc cs@(c :: more) =
      if isPrefixOf gs cs then pack (reverse acc) ++ pack (arrow (drop (length gs) cs)) else go (c :: acc) more

||| The name a binder group binds, `{auto 0 fx : T}` binding `fx`.
export
binderName : (tidy : String) -> Maybe String
binderName g =
  case dropWhile (\w => w `elem` the (List String) ["auto", "0", "1"]) (words (substr 1 (length g `minus` 2) g)) of
    (n :: ":" :: _) => Just n
    _ => Nothing
