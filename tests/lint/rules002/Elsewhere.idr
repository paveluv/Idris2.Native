||| A module named after nothing it defines: a reader looking for `found`
||| has to know it is here. Reported, as a warning.
module Elsewhere

%default total

||| Found here, under another name.
export
found : Nat
found = 2
