||| The refactoring `order-imports` (`orderImports`): a file's imports put in
||| order. Only the import block is rewritten, from its first import to its
||| last.
module Lint.Refactor.OrderImports

import Lint.Refactor.Change
import Lint.Refactor.Edit
import Lint.Refactor.Refactoring
import Lint.Refactor.Subject

import Core.FC
import Core.Name.Namespace
import Data.List
import Data.String
import Idris.Syntax
import Lint.Finding
import Lint.Rules
import Lint.Source

%default covering

||| `order-imports`: the file's imports in order, when they are not.
export
orderImports : Refactoring
orderImports = fileRefactoring "order-imports" "put each file's imports in order" candidates
  where
    ||| The file's lines with its imports in order, in their blocks
    ||| (`importBlock`): the public ones, those of the module's own group,
    ||| then the others, each block alphabetical as a reader sorts and set
    ||| apart from the next by a blank line. Each import keeps the comment lines between it and the import
    ||| before it, and whatever follows it on its own lines; comments above the
    ||| first import stay above the block, which they describe.
    orderedImports : SourceFile -> List String -> List String
    orderedImports f ls =
      let is = sortBy (\a, b => compare (span a) (span b)) f.mod.imports in
      case (is, last' is) of
        ([], _) => ls
        (_, Nothing) => ls
        (first :: _, Just lastImport) =>
          let blockStart = fst (span first)
              blockEnd = snd (span lastImport)
              chunks = chunksOf blockStart is
              sorted = sortBy (\a, b => compare (key a) (key b)) chunks
              block = joined (intersperse [""] (filter (not . null) (map (\b => chunkLines (filter (inBlock b) sorted)) [0, 1, 2])))
          in take (cast blockStart) ls ++ block ++ drop (cast (blockEnd + 1)) ls
      where
        key : (Import, List String) -> (Nat, String, String)
        key (i, _) = importKey (show f.mod.moduleNS) i

        inBlock : Nat -> (Import, List String) -> Bool
        inBlock b (i, _) = importBlock (show f.mod.moduleNS) i == b

        linesFrom : Int -> Int -> List String
        linesFrom a b = take (cast (b - a + 1)) (drop (cast a) ls)

        ||| The lines an import spans.
        span : Import -> (Int, Int)
        span i = case i.loc of
          MkFC _ (sl, _) (el, _) => (sl, el)
          MkVirtualFC _ (sl, _) (el, _) => (sl, el)
          EmptyFC => (-1, -1)

        -- each import with its lines: the non-blank lines after the previous
        -- import's, then its own
        chunksOf : Int -> List Import -> List (Import, List String)
        chunksOf _ [] = []
        chunksOf from (i :: rest) =
          let (s, e) = span i
              above = filter (\l => trim l /= "") (linesFrom from (s - 1))
          in (i, above ++ linesFrom s e) :: chunksOf (e + 1) rest

        chunkLines : List (Import, List String) -> List String
        chunkLines = foldr (\(_, l), rest => l ++ rest) []

    candidates : Subject -> List Candidate
    candidates s =
      let ls = linesOf s
          ordered = orderedImports s.file ls
      in if ordered == ls then [] else [MkCandidate "imports" (Right (inFile s.file.path [replaceAll s.text (unlines ordered)]))]
