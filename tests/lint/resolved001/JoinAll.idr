||| Appends, which `list-append` reports, a warning, per definition: each
||| `++` on lists, and `concat` at a list's monoid, copies its left list,
||| where a `Builder` (`Data.Builder`) joins in constant time and copies
||| once, when its contents are read.
module JoinAll

import Data.Builder

%default total

||| The lists joined, by `++` from the right: one append, though it runs
||| once for each list.
export
joinAll : List (List Nat) -> List Nat
joinAll = foldr (++) []

||| Three lists joined, by `++` twice.
export
joinThree : List Nat -> List Nat -> List Nat -> List Nat
joinThree xs ys zs = xs ++ ys ++ zs

||| The lists joined by `concat`, whose monoid is the list's: one append.
export
flatten : List (List Nat) -> List Nat
flatten = concat

||| Two builders joined, in constant time: a builder's append, not
||| reported, and counted in the score's `builders`.
export
joinBuilt : Builder Nat -> Builder Nat -> Builder Nat
joinBuilt a b = a <+> b
