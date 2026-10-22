||| A clause broken after its `=` that fits on one line (`SplitClause`):
||| broken when it did not fit, and left so when it came to, since breaking
||| a line that is too wide (`reflow-lines`) never joins one. What the rule
||| `split-clause` reports and `format` joins.
module Lint.SplitClause

import Lint.Source

import Core.FC
import Idris.Syntax
import Libraries.Data.WithData

%default covering

||| A clause whose right side is on the line after its `=`, all on that
||| line, and would fit after it: the clause, the line of its `=` and the
||| line of its right side, from 0.
public export
record SplitClause where
  constructor MkSplitClause
  clause : FC
  first : Int
  second : Int

||| The clauses of a file broken after their `=` that would fit on one line
||| at the width: a clause at the top, in a `where` block at any depth, in
||| a `mutual` block, a namespace, a parameter block, an interface's or an
||| implementation's body; not one with a comment on either line, which
||| joining would move, nor a `failing` block's.
export
splitClauses : (width : Int) -> Source.SourceFile -> List SplitClause
splitClauses width f = decls f.mod.decls
  where
    commented : Int -> Bool
    commented l = any (\c => c.line == l) f.comments

    -- the clause's own position runs to its last token, a term's not
    -- always (a tuple's covers less), so the clause must end on its right
    -- side's line: one with a `where` block is left as it is
    one : FC -> PTerm -> PTerm -> List SplitClause
    one fc lhs rhs = case (fc, getPTermLoc lhs, getPTermLoc rhs) of
      (MkFC _ _ (e, ec), MkFC _ _ (l, c), MkFC _ (l', c') _) =>
        if l' == l + 1 && e == l' && not (commented l || commented l')
           && c + 3 + (ec - c') <= width
          then [MkSplitClause fc l l'] else []
      _ => []

    mutual
      decls : List PDecl -> List SplitClause
      decls ds = foldr (\d, rest => decl d ++ rest) [] ds

      decl : PDecl -> List SplitClause
      decl d = case d.val of
        PDef cs => foldr (\c, rest => clause c ++ rest) [] cs
        PMutual ds => decls ds
        PNamespace _ ds => decls ds
        PParameters _ ds => decls ds
        PUsing _ ds => decls ds
        PInterface _ _ _ _ _ _ _ ds => decls ds
        PImplementation _ _ _ _ _ _ _ _ _ (Just ds) => decls ds
        _ => []

      clause : PClause -> List SplitClause
      clause (MkPatClause fc lhs rhs wh) = one fc lhs rhs ++ decls wh
      clause (MkWithClause _ _ _ _ cs) = foldr (\c, rest => clause c ++ rest) [] cs
      clause (MkImpossible _ _) = []
