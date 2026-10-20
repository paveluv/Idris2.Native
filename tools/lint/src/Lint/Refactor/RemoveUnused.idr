||| The refactoring `remove-unused` (`removeUnused`): a private function at
||| the top of a module that nothing uses is deleted, with its comments and
||| pragmas.
|||
||| A use is a reference that means the function: a declaration that binds a
||| name of its own spelled the same, a variable or a local function, does
||| not use it. Where the analysis does not follow a declaration (an
||| implementation, a data type), any mention of the name counts as a use.
||| Only private functions go, which nothing outside the module can use, and
||| none that is used without being named: not `main`, where a program
||| starts, nor a hint, which search finds; a function declared `%foreign`
||| or `%extern` is never one of them.
module Lint.Refactor.RemoveUnused

import Lint.Refactor.Change
import Lint.Refactor.Edit
import Lint.Refactor.Extent
import Lint.Refactor.Free
import Lint.Refactor.Refactoring
import Lint.Refactor.Subject

import Data.SortedSet
import Idris.Syntax
import Libraries.Data.WithData
import Lint.Rules
import Lint.Source
import TTImp.TTImp

%default covering

||| `remove-unused`: each private function at the top of a module that no
||| other declaration uses, deleted.
export
removeUnused : Refactoring
removeUnused =
  Refactoring.fileRefactoring "remove-unused"
    "delete each private function at the top of a module that nothing uses" candidates
  where
    -- whether a declaration, not one of the function's own, uses it
    uses : Rules.Declared -> Rules.Declared -> Bool
    uses f d =
      not (any (`elem` f.defines) d.defines) &&
        (let names = Free.inDecl d.decl in
         if contains Free.unknown names then any (`elem` f.defines) d.mentions
           else any (\n => contains n names) f.defines)

    -- whether the function is used without being named
    unnamedUse : Rules.Declared -> Bool
    unnamedUse f = ("main" `elem` f.defines) || case f.decl.val of
      PClaim c => any hint c.opts
      _ => False
      where
        hint : PFnOpt -> Bool
        hint (IFnOpt (Hint _)) = True
        hint (IFnOpt (GlobalHint _)) = True
        hint _ = False

    candidates : Subject -> List Refactoring.Candidate
    candidates s =
      map
        (\f =>
         Refactoring.candidate (Refactoring.labelOf f) (map (\e => Change.inFile s.file.path [Extent.cut (Subject.linesOf s) e]) (Extent.extentOf s f)))
          (filter (\f => Rules.privateAtTop f && not (unnamedUse f) && not (any (uses f) s.declared))
            s.declared)
