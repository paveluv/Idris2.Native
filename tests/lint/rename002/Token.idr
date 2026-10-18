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
