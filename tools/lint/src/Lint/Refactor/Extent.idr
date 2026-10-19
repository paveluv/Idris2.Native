||| Where a function is written (`Extent`): the lines of its claim and of its
||| clauses, with the comments and pragmas just above them, and the column
||| it starts at.
module Lint.Refactor.Extent

import Lint.Refactor.Edit
import Lint.Refactor.Span
import Lint.Refactor.Subject

import Core.FC
import Core.WithData
import Data.List
import Data.String
import Idris.Syntax
import Libraries.Data.WithData
import Lint.Rules
import Lint.Source

%default covering

||| The lines a function takes, from `first` to `last`, both included; the
||| column its claim starts at; and the text that moves with it: those
||| lines, but for the header of a block it was the last declaration of,
||| which goes with it.
public export
record Extent where
  constructor MkExtent
  first : Int
  last : Int
  column : Int
  text : List String
  ||| The source lines the text is made of, in ranges, both ends included.
  segments : List (Int, Int)

||| The first line of what is attached above a line: the comments, pragmas,
||| totality modifiers and visibility written just above it, with no blank
||| line between, which move with the declaration below them.
export
attachedFrom : List String -> (line : Int) -> Int
attachedFrom ls l = if l > 0 && maybe False attached (head' (drop (cast (l - 1)) ls))
  then attachedFrom ls (l - 1) else l
  where
    -- a line of nothing but visibility and totality: `public export`,
    -- `export covering`, `total`
    modifiers : String -> Bool
    modifiers t = t /= ""
      && all
        (`elem` the (List String) ["export", "public", "private", "total", "covering", "partial"])
          (words t)

    attached : String -> Bool
    attached x = let t = trim x in
      isPrefixOf "|||" t || isPrefixOf "--" t || isPrefixOf "%" t || modifiers t

||| The definitions of the names a claim declares, in the order written.
export
definitionsOf : Subject -> (claim : Declared) -> List Declared
definitionsOf s claim = filter defines s.declared
  where
    defines : Declared -> Bool
    defines d = case d.decl.val of
      PDef _ => any (`elem` claim.defines) d.defines
      _ => False

||| Where the function a claim declares is written: from the comments and
||| pragmas just above the claim to the end of its last clause. It is one
||| piece only if each of its names has a definition, after the claim, and
||| nothing else is declared between them. If it is all that is left of a
||| block (`mutual`, `parameters`, ...), the block's header goes, and the
||| comments above the header, which are about the block, move with it.
export
extentOf : Subject -> (claim : Declared) -> Either String Extent
extentOf s claim =
  let (cs, ce) = lineSpan claim.decl.fc
      defs = definitionsOf s claim
      spans = map (lineSpan . (.decl.fc)) defs
      end = foldl (\m, sp => max m (snd sp)) ce spans
  in if not (all (\n => any (\d => n `elem` d.defines) defs) claim.defines)
    then Left "a name it declares has no definition"
     else if any (\sp => fst sp < cs) spans then Left "it is defined before its claim"
     else if any (between cs end) (filter (not . ours defs) s.declared)
       then Left "other declarations lie between its claim and its definition"
     else Right (piece (attachedFrom (linesOf s) cs) end)
  where
    ours : List Declared -> Declared -> Bool
    ours defs d = lineSpan d.decl.fc == lineSpan claim.decl.fc
      || any (\o => lineSpan o.decl.fc == lineSpan d.decl.fc) defs

    between : Int -> Int -> Declared -> Bool
    between a b d = let l = fst (lineSpan d.decl.fc) in l >= a && l <= b

    linesFrom : Int -> Int -> List String
    linesFrom a b = take (cast (b - a + 1)) (drop (cast a) (linesOf s))

    ||| The blocks of a list of declarations, at any depth (`mutual`,
    ||| `parameters`, `namespace`, `using`): the line each starts at, and the
    ||| lines each of its declarations spans.
    blocksOf : List PDecl -> List (Int, List (Int, Int))
    blocksOf = foldr (\d, rest => here d ++ rest) []
      where
        block : PDecl -> List PDecl -> List (Int, List (Int, Int))
        block d ds = (fst (lineSpan d.fc), map (lineSpan . (.fc)) ds) :: blocksOf ds

        here : PDecl -> List (Int, List (Int, Int))
        here d = case d.val of
          PMutual ds => block d ds
          PNamespace _ ds => block d ds
          PParameters _ ds => block d ds
          PUsing _ ds => block d ds
          _ => []

    -- the function's lines, or those of the block it is all that is left
    -- of, without the block's header
    piece : Int -> Int -> Extent
    piece first last =
      let column = startColumn claim.decl.fc
          emptied = find (\(_, members) => any (\m => fst m >= first && fst m <= last) members
                                           && all (\m => fst m >= first && fst m <= last) members)
                                             (blocksOf s.file.mod.decls)
      in case emptied of
           Nothing => MkExtent first last column (linesFrom first last) [(first, last)]
           Just (header, _) =>
             let above = attachedFrom (linesOf s) header in
             MkExtent above last column (linesFrom above (header - 1) ++ linesFrom first last)
               [(above, header - 1), (first, last)]

||| The edit that takes a function's lines out, and one blank line beside
||| them if they stood between two.
export
cut : (text : List String) -> Extent -> Edit
cut ls e =
  if blankAt (e.last + 1) && (e.first == 0 || blankAt (e.first - 1))
    then deleteLines e.first (e.last + 1)
    else deleteLines e.first e.last
  where
    blankAt : Int -> Bool
    blankAt l = maybe False (\t => trim t == "") (head' (drop (cast l) ls))

||| A function's text taken from other lines of the same shape, such as the
||| file's with names renamed in place.
export
textOf : List String -> Extent -> List String
textOf ls e =
  foldr (\(a, b), rest => take (cast (b - a + 1)) (drop (cast a) ls) ++ rest) [] e.segments

||| Where a source line is in a function's text, if it is there.
export
indexIn : Extent -> (line : Int) -> Maybe Int
indexIn e l = go 0 e.segments
  where
    go : Int -> List (Int, Int) -> Maybe Int
    go _ [] = Nothing
    go at ((a, b) :: more) = if l >= a && l <= b then Just (at + l - a)
      else go (at + b - a + 1) more
