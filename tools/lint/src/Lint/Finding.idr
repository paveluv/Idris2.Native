||| What a rule reports: where, which rule, about what, and why. A finding
||| prints in two forms: with its position, for a person at the code; and
||| without, the rule, the file and the subject only, for the gate, so that
||| moving code does not change the gate's expected output.
module Lint.Finding

import Data.String

%default total

public export
record Finding where
  constructor MkFinding
  rule : String
  path : String
  ||| From 0, as Idris counts lines and columns.
  line : Int
  col : Int
  ||| What the finding is about, stable when code moves: a name, an import.
  subject : String
  message : String

export
Eq Finding where
  a == b = (a.path, a.line, a.col, a.rule, a.subject) == (b.path, b.line, b.col, b.rule, b.subject)

export
Ord Finding where
  compare a b = compare (a.path, a.line, a.col, a.rule, a.subject) (b.path, b.line, b.col, b.rule, b.subject)

||| `path:line:col rule: message`, lines and columns from 1.
export
withPosition : Finding -> String
withPosition f =
  f.path ++ ":" ++ show (f.line + 1) ++ ":" ++ show (f.col + 1) ++ " " ++ f.rule ++ ": " ++ f.message

||| `rule path subject`.
export
withoutPosition : Finding -> String
withoutPosition f = f.rule ++ " " ++ f.path ++ " " ++ f.subject

||| Lists joined from the right, each copied once: `concat` on lists joins
||| from the left and copies what it has joined at every step.
export
joined : List (List a) -> List a
joined = foldr (++) []
