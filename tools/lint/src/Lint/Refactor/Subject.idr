||| A file as a refactoring sees it (`Subject`): its parse, its declarations
||| with what each defines and mentions, and its text.
module Lint.Refactor.Subject

import Data.String
import Lint.Rules
import Lint.Source
import System.File.Error
import System.File.ReadWrite

%default covering

||| A parsed file with its declarations and its text.
public export
record Subject where
  constructor MkSubject
  file : SourceFile
  declared : List Declared
  text : String

||| The file's text, line by line.
export
linesOf : Subject -> List String
linesOf s = lines s.text

||| The file at the path, parsed, or what stopped it.
export
load : (path : String) -> IO (Either String Subject)
load path = do
  Right f <- parse path
    | Left e => pure (Left e)
  ds <- declared f
  Right t <- readFile path
    | Left e => pure (Left (show e))
  pure (Right (MkSubject f ds t))
