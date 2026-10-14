||| Code put into a clause's `where` block (`intoWhere`), which is made if the
||| clause has none.
module Lint.Refactor.Where

import Lint.Refactor.Edit
import Lint.Refactor.Extent
import Lint.Refactor.Free
import Lint.Refactor.Reindent
import Lint.Refactor.Span

import Core.FC
import Core.WithData
import Data.List
import Data.Maybe
import Data.SortedSet
import Idris.Syntax
import Libraries.Data.WithData
import Lint.Rules

%default covering

||| The source location of a clause.
export
clauseLoc : PClause -> FC
clauseLoc (MkPatClause fc _ _ _) = fc
clauseLoc (MkWithClause fc _ _ _ _) = fc
clauseLoc (MkImpossible fc _) = fc

||| The edit that puts a function's lines, which start at column `column`,
||| into the clause's `where` block, at the depth of the definitions there.
||| A local function is defined before it is used, as at the top of a
||| module: the lines go just above the first local function that uses one
||| of the `names` they define, with that one's comments, or at the end if
||| none does; and they cannot go in if they use (`uses`) a local function
||| written at or after that place. A clause with no `where` block gets
||| one, two columns in from the clause, its definitions two further.
export
intoWhere : (text : List String) -> PClause -> (names : List String) -> (uses : SortedSet String) ->
            (column : Int) -> List String -> Either String Edit
intoWhere _ (MkPatClause fc _ _ []) _ _ column ls =
  let at = startColumn fc in
  Right (insertLines (snd (lineSpan fc) + 1) ((pack (List.replicate (cast (at + 2)) ' ') ++ "where") :: reindent column (at + 4) ls))
intoWhere text (MkPatClause fc _ _ wh@(d :: _)) names uses column ls =
  let depth = startColumn d.fc in
  case find (\w => any (\n => contains n (inDecl w)) names) wh of
    Nothing =>
      let end = foldl (\m, w => max m (snd (lineSpan w.fc))) (snd (lineSpan fc)) wh in
      Right (insertLines (end + 1) ("" :: reindent column depth ls))
    Just user =>
      -- the user's function starts with its claim, the first local
      -- declaration of one of its names
      let userNames = definesOf user
          first = fromMaybe user (find (\w => any (`elem` userNames) (definesOf w)) wh)
          from = fst (lineSpan first.fc)
          after = filter (\w => fst (lineSpan w.fc) >= from) wh
      in if any (\w => any (\n => contains n uses) (definesOf w)) after
           then Left "it uses a local function its user's `where` block defines after the one that uses it"
           else Right (insertLines (attachedFrom text from) (reindent column depth ls ++ [""]))
intoWhere _ (MkWithClause _ _ _ _ _) _ _ _ _ = Left "the clause is a `with` clause"
intoWhere _ (MkImpossible _ _) _ _ _ _ = Left "the clause is impossible"
