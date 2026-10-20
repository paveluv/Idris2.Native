||| A file as a refactoring sees it (`Subject`): its parse, its declarations
||| with what each defines and mentions, and its text.
module Lint.Refactor.Subject

import Core.FC
import Core.Name
import Data.List
import Data.String
import Idris.Syntax
import Lint.Rules
import Lint.Source
import System.File.Error
import System.File.ReadWrite

%default covering

||| A parsed file with its declarations and its text.
public export
record Subject where
  constructor MkSubject
  file : Source.SourceFile
  declared : List Rules.Declared
  text : String
  ||| The names its declarations write, each where it is written.
  written : List (FC, Name)
  ||| The names its declarations apply, each with its arguments.
  applied : List Rules.Applied

||| The file's text, line by line.
export
linesOf : Subject -> List String
linesOf s = lines s.text

||| A line of the file, or an empty one past its end.
export
lineOf : Subject -> Int -> String
lineOf s l = case drop (cast l) (linesOf s) of
  (x :: _) => x
  [] => ""

||| The file's lines from `a` to `b`, both included.
export
linesBetween : Subject -> (a, b : Int) -> List String
linesBetween s a b = take (cast (b - a + 1)) (drop (cast a) (linesOf s))

||| The file at the path, parsed, or what stopped it.
export
load : (path : String) -> IO (Either String Subject)
load path = do
  Right f <- Source.parse path
    | Left e => pure (Left e)
  ds <- declared f
  Right t <- readFile path
    | Left e => pure (Left (show e))
  ms <- Rules.mentions f.mod.decls
  pure (Right (MkSubject f ds t ms.refs ms.applied))
