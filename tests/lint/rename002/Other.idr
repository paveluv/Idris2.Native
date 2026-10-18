||| A module with a `Tok` of its own, which takes nothing from `Token`:
||| nothing here is renamed.
module Other

%default total

data Tok = MkTok

other : Tok
other = MkTok
