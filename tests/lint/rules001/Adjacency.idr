||| Implementations next to their types. `Colour`'s follow it, with the helper
||| its `Eq` uses between them: not reported. `Shade`'s `Show` comes after a
||| function that has nothing to do with it: reported. `Whole`'s `Show` uses
||| `parts`, which names `Part`, whose `Show` it uses in turn: all three
||| stand between `Whole` and its `Show` as its family, not reported.
module Adjacency

%default total

data Colour = Red | Green

||| The colour's number, which its `Eq` compares.
code : Colour -> Nat
code Red = 0
code Green = 1

Eq Colour where
  a == b = code a == code b

Show Colour where
  show Red = "red"
  show Green = "green"

data Shade = Light | Dark

||| Twice a number: nothing to do with `Shade`.
double : Nat -> Nat
double n = n + n

Show Shade where
  show Light = "light"
  show Dark = "dark"

data Whole = MkWhole Nat

data Part = Size

Show Part where
  show Size = "size"

||| A whole's parts, with their values.
parts : Whole -> List (Part, Nat)
parts (MkWhole n) = [(Size, n)]

Show Whole where
  show w = fastConcat (map (\pn => show (fst pn) ++ "=" ++ show (snd pn)) (parts w))
