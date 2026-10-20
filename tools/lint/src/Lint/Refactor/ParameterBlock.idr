||| A `parameters` block as a refactoring sees it (`ParameterBlock`): the
||| lines it spans, the names it binds, and its binders as written.
|||
||| Within the block each function takes the parameters without naming them.
||| A function moved out of a block whose parameters are all implicit takes
||| them as binders of its own type, and its calls, which never pass an
||| implicit, stay as they are.
module Lint.Refactor.ParameterBlock

import Lint.Refactor.Binders
import Lint.Refactor.Extent
import Lint.Refactor.Free
import Lint.Refactor.Span

import Core.Name
import Core.WithData
import Data.List
import Data.List1
import Data.SortedSet
import Data.String
import Idris.Syntax
import Libraries.Data.WithData

%default covering

||| A `parameters` block: its lines, the names it binds (those of its
||| binders, and the variables their types leave free, which it binds
||| implicitly, `enc` in `(d : Decls enc)`), and its binders as written,
||| each a bracketed group (`{enc : Enc}`, `(d : Decls enc)`).
public export
record ParameterBlock where
  constructor MkParameterBlock
  span : (Int, Int)
  names : SortedSet String
  binders : List String

||| The `parameters` blocks of a file, at any depth.
export
parameterBlocks : (text : List String) -> List PDecl -> List ParameterBlock
parameterBlocks text = foldr (\d, rest => here d ++ rest) []
  where
    -- the names the block binds, and the variables its binders' types
    -- leave free, which the block binds implicitly
    namesOf : Either (List1 PlainBinder) (List1 PBinder) -> SortedSet String
    namesOf (Left bs) =
      foldr (\b, rest => insert (nameRoot b.nameVal) (union (Free.typeVariables empty b.val) rest)) empty
        (forget bs)
    namesOf (Right bs) =
      foldr (\b,
        rest =>
          union (fromList (map (nameRoot . (.val)) (forget b.bind.names)))
             (union (Free.typeVariables empty b.bind.type) rest))
          empty (forget bs)

    -- the block's binders: the groups between the `parameters` keyword and
    -- its first declaration, with what is attached above that
    bindersAt : List String -> (from, to : Int) -> List String
    bindersAt ls from to =
      let header = take (cast (to - from)) (drop (cast from) ls) in
      map snd (Binders.binderGroups (unwords (afterKeyword header)))
      where
        afterKeyword : List String -> List String
        afterKeyword [] = []
        afterKeyword (x :: more) =
          let u = ltrim x in
          (if isPrefixOf "parameters" u then substr 10 (length u) u else u) :: more

    -- where the block's first declaration starts, its attached comments
    -- included, or the block's end
    firstOf : PDecl -> List PDecl -> Int
    firstOf d ds = case sort (map (fst . Span.lineSpan . (.fc)) ds) of
      (l :: _) => Extent.attachedFrom text l
      [] => snd (Span.lineSpan d.fc) + 1

    here : PDecl -> List ParameterBlock
    here d = case d.val of
      PParameters ps ds =>
        MkParameterBlock (Span.lineSpan d.fc) (namesOf ps)
          (bindersAt text (fst (Span.lineSpan d.fc)) (firstOf d ds)) :: parameterBlocks text ds
      PNamespace _ ds => parameterBlocks text ds
      PMutual ds => parameterBlocks text ds
      PUsing _ ds => parameterBlocks text ds
      _ => []

||| The block a line is in, if any.
export
blockAt : List ParameterBlock -> Int -> Maybe ParameterBlock
blockAt bs l = find (\b => l >= fst b.span && l <= snd b.span) bs

||| Whether two blocks bind the same parameters, as written.
export
sameParameters : ParameterBlock -> ParameterBlock -> Bool
sameParameters a b = a.span == b.span || a.binders == b.binders

||| Whether every parameter of the block is implicit, so that no call of a
||| function of it passes one.
export
implicitOnly : ParameterBlock -> Bool
implicitOnly b = all (isPrefixOf "{") b.binders

||| The block's binders as the start of a type, `{p : P} -> `, what a
||| function moved out of the block takes them as: those the place it goes
||| to does not provide (`provided`) already, which it uses as they are.
export
binderPrefix : (provided : String -> Bool) -> ParameterBlock -> String
binderPrefix provided b = fastConcat (map (++ " -> ") (filter (not . provided) b.binders))
