||| The refactoring `format` (`format`): the layout the code keeps, made
||| where it is not. Each signature's lines past its first start where
||| they belong (`Signature.aligned`), its line breaks kept; then each
||| clause broken after its `=` that fits on one line is joined
||| (`SplitClause`); then each line wider than the width is broken into
||| lines that fit (`reflow-lines`), a signature's as the signature's own
||| lines are. A file it leaves as it is has the layout already.
module Lint.Refactor.Format

import Lint.Refactor.Change
import Lint.Refactor.Edit
import Lint.Refactor.Refactoring
import Lint.Refactor.ReflowLines
import Lint.Refactor.Signature
import Lint.Refactor.Subject

import Data.String
import Lint.Source
import Lint.SplitClause

%default covering

||| Each signature whose lines past its first start elsewhere than they
||| belong, its lines realigned: all of them, then each alone.
realigned : Subject -> List Refactoring.Candidate
realigned s = case moved of
  [] => []
  ms =>
    Refactoring.candidate "signatures aligned"
      (Right (Change.inFile s.file.path [ e | (_, e) <- ms ]))
      :: [ Refactoring.candidate ("the signature at line " ++ show (g.first + 1))
             (Right (Change.inFile s.file.path [e]))
         | (g, e) <- ms ]
  where
    moved : List (Signature, Edit)
    moved =
      mapMaybe
        (\g =>
          let ls = Subject.linesBetween s g.first g.last
              ls' = Signature.aligned g.column ls
          in if ls == ls' then Nothing else Just (g, Edit.replaceLines g.first g.last ls'))
        (Signature.subjectSignatures s)

||| Each clause broken after its `=` that fits on one line at the width,
||| joined: all of them, then each alone.
joined : (width : Int) -> Subject -> List Refactoring.Candidate
joined width s = case splits of
  [] => []
  cs =>
    Refactoring.candidate "clauses joined" (Right (Change.inFile s.file.path [ e | (_, e) <- cs ]))
      :: [ Refactoring.candidate ("the clause at line " ++ show (c.first + 1))
             (Right (Change.inFile s.file.path [e]))
         | (c, e) <- cs ]
  where
    splits : List (SplitClause, Edit)
    splits =
      [ (c, Edit.replaceLines c.first c.second
              [rtrim (Subject.subjectLine s c.first) ++ " " ++ trim (Subject.subjectLine s c.second)])
      | c <- SplitClause.splitClauses width s.file ]

||| `format`: the signatures aligned, then the clauses that fit on one line
||| joined, then the lines wider than the width (`--arg WIDTH`, 100 by
||| default) broken.
export
format : (arguments : List String) -> Refactoring
format args =
  Refactoring.fileRefactoring "format"
    ("align each signature's lines with its type, join each clause broken after its `=` that "
     ++ "fits on one line, then break each line wider than a width (--arg WIDTH, 100 by "
     ++ "default) into lines that fit")
    (\s => case realigned s of
             [] => case joined (ReflowLines.argsWidth args) s of
               [] => ReflowLines.wideLines (ReflowLines.argsWidth args) s
               cs => cs
             cs => cs)
