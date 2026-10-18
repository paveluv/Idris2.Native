||| Taking a value for one of another type: `believe_me` and
||| `really_believe_me` are reported (`cast`), and a suppression of them is a
||| finding itself, as no reason lifts the rule.
module Casts

%default total

asNat : Bits64 -> Nat
asNat w = believe_me w

-- lint: allow cast: it is a word either way
asInt : Bits64 -> Int
asInt w = really_believe_me w
