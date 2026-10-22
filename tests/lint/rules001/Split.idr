||| Clauses broken after their `=`: `split-clause` for `twice`, whose right
||| side fits after it. None for `wide`, whose right side would not fit,
||| `same`, with a comment after its `=`, `pair`, whose right side is two
||| lines, and `helped`, with a `where` block.
module Split

%default total

twice : Nat -> Nat
twice n =
  n + n

wide : Nat -> Nat
wide n =
  n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n

same : Nat -> Nat
same n = -- the number, unchanged
  n

pair : Nat -> (Nat, Nat)
pair n =
  (n,
   n)

helped : Nat -> Nat
helped n =
  go n
  where
    go : Nat -> Nat
    go m = m
