||| Helpers that `scope-helpers` leaves where they are, each with why.
module Stays

%default total

-- Used by two clauses of its user: a `where` block belongs to one clause,
-- so the helper would be written twice.

half : Integer -> Integer
half n = div n 2

export
halfOr : Integer -> Maybe Integer -> Integer
halfOr d Nothing = half d
halfOr _ (Just n) = half n

-- A helper using a name that its user's clause binds as a variable: in the
-- user's block, `limit` would be the variable, not the function.

export
limit : Nat
limit = 10

capped : Nat -> Nat
capped n = min n limit

export
clamp : (limit : Nat) -> Nat -> Nat
clamp limit n = if n > limit then capped limit else capped n

-- A helper in a block of explicit parameters, used outside it: each call
-- passes the parameter, and moved out of the block it would take one more
-- argument.

parameters (base : Nat)
  offset : Nat -> Nat
  offset n = base + n

export
shifted : Nat -> Nat
shifted n = offset 5 n
