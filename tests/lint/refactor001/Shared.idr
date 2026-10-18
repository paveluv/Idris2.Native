||| Helpers whose type variables have the names of their users' own, so
||| that moved into their users they could mean the users' or stay their
||| own. Which one only the type checker can judge: with a check, a helper
||| is moved as it is first, its constraint gone where its user has it, and
||| kept general, its variable renamed, only if that does not check.
module Shared

%default total

interface Sized a where
  size : a -> Nat

-- Used only at its user's `a`: moved as it is, without `Sized a =>`,
-- which search finds in its user's.
twice : Sized a => a -> Nat
twice x = size x + size x

export
total2 : Sized a => a -> a -> Nat
total2 x y = twice x + twice y

-- Used at its user's `a` and at its `b`: kept general where it goes, as
-- `Sized a' => a' -> Nat`.
one : Sized a => a -> Nat
one x = size x

export
both : Sized a => Sized b => a -> b -> Nat
both x y = one x + one y
