||| An import kept for the flat check: a finding of its suppression, as the
||| check loads every module a flat function reaches itself, so a module
||| imports only what it uses.
module ForFlat

-- lint: allow import-unused: the flat check reaches through a helper's body, which uses it
import Data.List

%default total

answer : Nat
answer = 42
