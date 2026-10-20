||| The module whose names are renamed: a token, its type and its
||| constructor, which the test renames to `Ordo` and `MkOrdo`. In its own
||| module every use of the name in code is the module's own; the comments
||| that say `Tok` stay as they are, for a person to rewrite.
module Token

%default total

||| The token.
public export
data Tok : Type where
  MkTok : Tok

||| A token used: its one value matched.
export
spend : Tok -> Nat
spend MkTok = 1

||| Two tokens' worth, by a helper of its own in a `where` block, which
||| the test renames with `spend`, both in one run: a local name in its
||| module alone.
export
double : Tok -> Nat
double t = costOf t + costOf t
  where
    costOf : Tok -> Nat
    costOf = spend
