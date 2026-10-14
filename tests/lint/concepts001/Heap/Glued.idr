||| Two functions their importers use apart, each long enough to stand
||| alone, but both use one private helper: a split would have to export
||| it, so `separation` sees one piece.
module Heap.Glued

%default total

-- the helper both use, private to the module
scaled : Nat -> Nat
scaled n = n * 8

||| The first of the two: `Places` uses it, and `Bits` does not.
export
offsetOf : Nat -> Nat
offsetOf Z = 0
offsetOf (S Z) = scaled 1
offsetOf (S (S Z)) = scaled 2
offsetOf (S (S (S Z))) = scaled 3
offsetOf (S (S (S (S Z)))) = scaled 4
offsetOf (S (S (S (S (S Z))))) = scaled 5
offsetOf (S (S (S (S (S (S Z)))))) = scaled 6
offsetOf (S (S (S (S (S (S (S Z))))))) = scaled 7
offsetOf n = scaled n

||| The second: `Bits` uses it, and `Places` does not.
export
spanOf : Nat -> Nat
spanOf Z = 0
spanOf (S Z) = scaled 1 + 1
spanOf (S (S Z)) = scaled 2 + 1
spanOf (S (S (S Z))) = scaled 3 + 1
spanOf (S (S (S (S Z)))) = scaled 4 + 1
spanOf (S (S (S (S (S Z))))) = scaled 5 + 1
spanOf (S (S (S (S (S (S Z)))))) = scaled 6 + 1
spanOf (S (S (S (S (S (S (S Z))))))) = scaled 7 + 1
spanOf n = scaled n + 1
