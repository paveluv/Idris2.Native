||| Lines moved to another depth (`reindent`), their layout among themselves
||| kept.
module Lint.Refactor.Reindent

import Data.List
import Data.String

%default total

||| Lines that start at column `from` moved to start at column `to`: each
||| keeps its indentation relative to `from`, a blank line stays blank, and
||| a line indented less than `from` starts at `to`.
export
reindent : (from, to : Int) -> List String -> List String
reindent from to = map one
  where
    one : String -> String
    one l =
      if trim l == "" then "" else
        let body = ltrim l
            depth = cast {to = Int} (length l) - cast (length body)
            new = to + max 0 (depth - from)
        in pack (replicate (cast new) ' ') ++ body
