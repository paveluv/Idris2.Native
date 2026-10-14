||| A source file as the linter sees it: Idris's own parse of it, the module
||| with its imports and its declarations, and its comments, each with its
||| position and its text. Plain comments come from the parser's state, which
||| keeps where each one is; documentation comments from the lexer, which
||| gives each `|||` line as a token.
module Lint.Source

import Core.Core
import Core.FC
import Core.Metadata
import Data.List
import Data.String
import Idris.Parser
import Idris.Syntax
import Libraries.Text.Bounded
import Libraries.Text.Lexer.Core
import Parser.Lexer.Source
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
  ||| How many lines the file has.
  lineCount : Nat

||| The file at the path, parsed, or what stopped the parse.
export
parse : (path : String) -> IO (Either String SourceFile)
parse path = do
  Right text <- readFile path
    | Left err => pure (Left (path ++ ": " ++ show err))
  let origin = PhysicalPkgSrc path
      ls = lines text
  case runParser origin Nothing text (prog origin) of
    Left err => pure (Left (path ++ ": does not parse: " ++ show err))
    Right (_, st, m) => do
      let plain = mapMaybe (plainComment ls) st.decorations
          docs = case lexTo (pred (const False)) text of
                   Left _ => the (List SourceComment) []
                   Right (_, toks) => mapMaybe docComment toks
      pure (Right (MkSourceFile path m (sortBy (\a, b => compare (a.line, a.col) (b.line, b.col)) (plain ++ docs)) (blank 0 ls) (length ls)))
  where
    ||| The text between two positions of a file given as its lines.
    slice : List String -> (start, end : (Int, Int)) -> String
    slice ls (sl, sc) (el, ec) =
      let inside = take (cast (el - sl + 1)) (drop (cast sl) ls) in
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

    -- the parser records a documentation block as a comment too; those come
    -- from the lexer, a line each
    plainComment : List String -> ASemanticDecoration -> Maybe SourceComment
    plainComment ls ((_, s, e), Comment, _) =
      let t = slice ls s e in
      if isPrefixOf "|||" (trim t) then Nothing else Just (MkSourceComment (fst s) (snd s) False (unmarked t))
    plainComment _ _ = Nothing

    blank : Int -> List String -> List Int
    blank _ [] = []
    blank i (l :: rest) = if trim l == "" then i :: blank (i + 1) rest else blank (i + 1) rest

    docComment : WithBounds Token -> Maybe SourceComment
    docComment t = case t.val of
      DocComment c => Just (MkSourceComment t.bounds.startLine t.bounds.startCol True c)
      _ => Nothing
