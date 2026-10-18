||| A source file as the linter sees it: Idris's own parse of it, the module
||| with its imports and its declarations, and its comments, each with its
||| position and its text, all from the parser's state, which keeps where
||| each comment is: a plain one, or a documentation block, a comment for
||| each of its `|||` lines.
module Lint.Source

import Core.Core
import Core.FC
import Core.Metadata
import Data.List
import Data.SortedMap
import Data.String
import Data.Zippable
import Idris.Parser
import Idris.Syntax
import Parser.Rule.Source
import Parser.Source
import Protocol.IDE.Decoration
import System.File.Error
import System.File.ReadWrite

%default covering

||| A comment: where it starts (lines and columns from 0, as Idris counts
||| them), whether it is documentation (`|||`), and its text without the
||| marker.
public export
record SourceComment where
  constructor MkSourceComment
  line : Int
  col : Int
  isDoc : Bool
  text : String

||| A parsed file.
public export
record SourceFile where
  constructor MkSourceFile
  path : String
  mod : Module
  comments : List SourceComment
  ||| The lines with nothing on them, in order.
  blankLines : List Int

||| The file at the path, parsed, or what stopped the parse.
export
parse : (path : String) -> IO (Either String SourceFile)
parse path = do
  Right text <- readFile path
    | Left err => pure (Left (path ++ ": " ++ show err))
  let origin = PhysicalPkgSrc path
      ls = lines text
      numbered = the (SortedMap Int String) (fromList (zip [0 .. cast (length ls)] ls))
  case runParser origin Nothing text (prog origin) of
    Left err => pure (Left (path ++ ": does not parse: " ++ show err))
    Right (_, st, m) => do
      let cs = nubBy (\a, b => (a.line, a.col) == (b.line, b.col)) (foldr (\d, rest => comments numbered d ++ rest) [] st.decorations)
      pure (Right (MkSourceFile path m (sortBy (\a, b => compare (a.line, a.col) (b.line, b.col)) cs) (blank 0 ls)))
  where
    ||| The text between two positions of a file given as its lines, by
    ||| number.
    slice : SortedMap Int String -> (start, end : (Int, Int)) -> String
    slice ls (sl, sc) (el, ec) =
      let inside = mapMaybe (\l => lookup l ls) [sl .. el] in
      case inside of
        [] => ""
        [one] => substr (cast sc) (cast (ec - sc)) one
        (first :: rest) =>
          fastConcat (intersperse "\n" (substr (cast sc) (length first) first :: init' rest
                                       ++ maybe [] (\l => [substr 0 (cast ec) l]) (last' rest)))
      where
        init' : List String -> List String
        init' [] = []
        init' [_] = []
        init' (x :: xs) = x :: init' xs

    ||| The text of a plain comment without its markers: `--`, or `{-` and `-}`.
    unmarked : String -> String
    unmarked s =
      let t = trim s in
      if isPrefixOf "--" t then trim (pack (drop 2 (unpack t)))
      else if isPrefixOf "{-" t then trim (pack (dropEnd 2 (drop 2 (unpack t))))
      else t
      where
        dropEnd : Nat -> List Char -> List Char
        dropEnd n xs = take (minus (length xs) n) xs

    -- a documentation line's text, as Idris's lexer gives it: after the
    -- marker, without one space
    documented : String -> String
    documented l =
      let rest = substr 3 (length l) l in
      if isPrefixOf " " rest then substr 1 (length rest) rest else rest

    -- the comments a decoration of the parser records: a plain comment, or
    -- a documentation block, a comment for each of its lines
    comments : SortedMap Int String -> ASemanticDecoration -> List SourceComment
    comments ls ((_, s, e), Comment, _) =
      let t = slice ls s e in
      if not (isPrefixOf "|||" (trim t)) then [MkSourceComment (fst s) (snd s) False (unmarked t)]
      else [ MkSourceComment (fst s + cast i) (if i == 0 then snd s else cast (length l `minus` length (ltrim l))) True (documented (ltrim l))
           | (i, l) <- zip [0 .. length (lines t)] (lines t), isPrefixOf "|||" (ltrim l) ]
    comments _ _ = []

    blank : Int -> List String -> List Int
    blank _ [] = []
    blank i (l :: rest) = if trim l == "" then i :: blank (i + 1) rest else blank (i + 1) rest

