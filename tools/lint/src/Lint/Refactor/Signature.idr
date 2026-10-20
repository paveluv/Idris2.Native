||| The signatures of a file (`Signature`), and where each of their lines
||| past the first starts (`aligned`): at the column of the signature's
||| type, or, where the line starts inside a bracket the signature opens
||| on a line before, one past the bracket, at a closing bracket at the
||| bracket itself. So a signature broken over lines reads as one type.
|||
||| A signature is a function's, a method's or a data constructor's, at the
||| top of the file or in a `where` block, a `mutual` block, a namespace,
||| a parameter block, an interface or an implementation. Its type starts
||| on its first line, after its names' `: `; one whose type starts on a
||| line of its own is not taken.
module Lint.Refactor.Signature

import Lint.Refactor.Span
import Lint.Refactor.Subject

import Core.FC
import Core.WithData
import Data.List
import Data.String
import Data.Zippable
import Idris.Syntax
import Libraries.Data.WithData
import Lint.Source

%default covering

||| A signature: its first and last lines, from 0, and the column its type
||| starts at on the first.
public export
record Signature where
  constructor MkSignature
  first : Int
  last : Int
  column : Int

||| The signatures of a file, in order.
export
signaturesOf : Subject -> List Signature
signaturesOf s = sortBy (\a, b => compare a.first b.first) (decls s.file.mod.decls)
  where
    typeDecl : PTypeDecl -> List Signature
    typeDecl t = case (Span.bounds t.fc, Span.bounds (getPTermLoc t.val.type)) of
      (Just ((l, _), (l', _)), Just ((tl, tc), _)) => if tl == l then [MkSignature l l' tc] else []
      _ => []

    mutual
      decls : List PDecl -> List Signature
      decls ds = foldr (\d, rest => decl d ++ rest) [] ds

      decl : PDecl -> List Signature
      decl d = case d.val of
        PClaim c => typeDecl c.type
        PData _ _ _ (MkPData _ _ _ _ cons) => foldr (\t, rest => typeDecl t ++ rest) [] cons
        PDef cs => foldr (\c, rest => clause c ++ rest) [] cs
        PMutual ds => decls ds
        PNamespace _ ds => decls ds
        PParameters _ ds => decls ds
        PUsing _ ds => decls ds
        PFail _ ds => decls ds
        PInterface _ _ _ _ _ _ _ ds => decls ds
        PImplementation _ _ _ _ _ _ _ _ _ (Just ds) => decls ds
        _ => []

      clause : PClause -> List Signature
      clause (MkPatClause _ _ _ wh) = decls wh
      clause (MkWithClause _ _ _ _ cs) = foldr (\c, rest => clause c ++ rest) [] cs
      clause (MkImpossible _ _) = []

||| The lines of a signature, its first as it is and each after it starting
||| where it belongs: at the type's column, inside a bracket one past it,
||| at a closing bracket at the bracket; a blank line stays blank.
export
aligned : (column : Int) -> List String -> List String
aligned c [] = []
aligned c (l :: ls) = l :: go (scan [] (unpack l) 0) ls
  where
    isOpChar : Char -> Bool
    isOpChar x = x `elem` unpack ":!#$%&*+./<=>?@\\^|-~"

    -- the brackets open, innermost first, by their columns, after the
    -- characters from the column: strings, character literals and a
    -- comment's text read past
    scan : List Int -> List Char -> Int -> List Int
    scan brackets [] _ = brackets
    scan brackets ('"' :: rest) i = inString brackets rest (i + 1)
      where
        inString : List Int -> List Char -> Int -> List Int
        inString brackets ('\\' :: _ :: more) j = inString brackets more (j + 2)
        inString brackets ('"' :: more) j = scan brackets more (j + 1)
        inString brackets (_ :: more) j = inString brackets more (j + 1)
        inString brackets [] _ = brackets
    scan brackets ('\'' :: '\\' :: _ :: '\'' :: rest) i = scan brackets rest (i + 4)
    scan brackets ('\'' :: _ :: '\'' :: rest) i = scan brackets rest (i + 3)
    scan brackets ('-' :: '-' :: rest) i =
      if maybe True (not . isOpChar) (head' rest) then brackets else scan brackets rest (i + 2)
    scan brackets (x :: rest) i =
      if x `elem` unpack "([{" then scan (i :: brackets) rest (i + 1)
      else if x `elem` unpack ")]}" then scan (drop 1 brackets) rest (i + 1)
      else scan brackets rest (i + 1)

    go : List Int -> List String -> List String
    go _ [] = []
    go brackets (l :: ls) =
      let body = ltrim l in
      if body == "" then "" :: go brackets ls else
        let at = case (brackets, unpack body) of
                   ([], _) => c
                   (b :: _, x :: _) => if x `elem` unpack ")]}" then b else b + 1
                   (b :: _, []) => b + 1
            l' = pack (replicate (cast at) ' ') ++ body
        in l' :: go (scan brackets (unpack l') 0) ls

||| Each line past a signature's first, from 0, with the column its
||| text belongs at (`aligned`).
export
continuations : Subject -> List (Int, Int)
continuations s = foldr (\g, rest => columns g ++ rest) [] (signaturesOf s)
  where
    columns : Signature -> List (Int, Int)
    columns g =
      let ls = Subject.linesBetween s g.first g.last
          lined = zip [g.first .. g.last] (aligned g.column ls)
      in [ (i, cast (length (takeWhile (== ' ') (unpack l)))) | (i, l) <- drop 1 lined ]
