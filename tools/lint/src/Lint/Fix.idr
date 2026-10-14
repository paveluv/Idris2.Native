||| What the linter fixes by itself: the order of a file's imports. Only the
||| import block is rewritten, from its first import to its last.
module Lint.Fix

import Core.FC
import Core.Name.Namespace
import Data.List
import Data.String
import Idris.Syntax
import Lint.Source

%default covering

||| The lines an import spans.
span : Import -> (Int, Int)
span i = case i.loc of
  MkFC _ (sl, _) (el, _) => (sl, el)
  MkVirtualFC _ (sl, _) (el, _) => (sl, el)
  EmptyFC => (-1, -1)

||| The file's lines with its imports in order: the public imports, then a
||| blank line, then the private ones, each block alphabetical as a reader
||| sorts. Each import keeps the comment lines between it and the import
||| before it, and whatever follows it on its own lines; comments above the
||| first import stay above the block, which they describe.
export
orderImports : SourceFile -> List String -> List String
orderImports f ls =
  let is = sortBy (\a, b => compare (span a) (span b)) f.mod.imports in
  case (is, last' is) of
    ([], _) => ls
    (_, Nothing) => ls
    (first :: _, Just lastImport) =>
      let blockStart = fst (span first)
          blockEnd = snd (span lastImport)
          chunks = chunksOf blockStart is
          sorted = sortBy (\a, b => compare (key a) (key b)) chunks
          (publics, privates) = partition isPublic sorted
          block = linesOf publics
                  ++ (if null publics || null privates then [] else [""])
                  ++ linesOf privates
      in take (cast blockStart) ls ++ block ++ drop (cast (blockEnd + 1)) ls
  where
    key : (Import, List String) -> (Bool, String, String)
    key (i, _) = (not i.reexport, toLower (show i.path), show i.path)

    linesFrom : Int -> Int -> List String
    linesFrom a b = take (cast (b - a + 1)) (drop (cast a) ls)

    -- each import with its lines: the non-blank lines after the previous
    -- import's, then its own
    chunksOf : Int -> List Import -> List (Import, List String)
    chunksOf _ [] = []
    chunksOf from (i :: rest) =
      let (s, e) = span i
          above = filter (\l => trim l /= "") (linesFrom from (s - 1))
      in (i, above ++ linesFrom s e) :: chunksOf (e + 1) rest

    isPublic : (Import, List String) -> Bool
    isPublic (i, _) = i.reexport

    linesOf : List (Import, List String) -> List String
    linesOf = foldr (\(_, l), rest => l ++ rest) []
