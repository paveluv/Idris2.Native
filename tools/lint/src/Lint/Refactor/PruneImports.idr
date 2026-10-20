||| The refactoring `prune-imports` (`pruneImports`): each private import of
||| a file removed, one at a time, and left out only if the file still
||| checks.
|||
||| Whether a module needs an import is the type checker's to say: a name
||| written, a type an implicit argument has, an implementation found by
||| search. So the refactoring runs only with a check, which undoes each
||| removal the module does not check without. A public import is another
||| module's too, its importers', and stays.
module Lint.Refactor.PruneImports

import Lint.Refactor.Change
import Lint.Refactor.Edit
import Lint.Refactor.Project
import Lint.Refactor.Refactoring
import Lint.Refactor.Span
import Lint.Refactor.Subject

import Core.Name.Namespace
import Data.String
import Idris.Syntax
import Lint.Source

%default covering

||| `prune-imports`: each private import the file checks without removed.
export
pruneImports : Refactoring
pruneImports =
  MkRefactoring "prune-imports"
    "remove each private import a file checks without; only with a check" False True
      (\_ => candidates)
  where
    candidates : Subject -> List Refactoring.Candidate
    candidates s =
      [ Refactoring.candidate ("import " ++ show i.path)
        (Right (Change.inFile s.file.path [removal s (fst (Span.lineSpan i.loc))]))
      | i <- s.file.mod.imports, not i.reexport ]
      where
        -- the import's line, and a blank line after it if one is before it:
        -- the last import of a block takes the block's blank line with it
        removal : Subject -> Int -> Edit
        removal s l = if trim (Subject.lineOf s (l - 1)) == "" && trim (Subject.lineOf s (l + 1)) == ""
          then Edit.deleteLines l (l + 1) else Edit.deleteLines l l
