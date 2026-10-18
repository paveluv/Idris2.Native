||| Local functions with primed type variables, as `scope-helpers` moves
||| them without a check: each kept as general as it was. `unprime` gives a
||| variable back the name of its user's where that checks: there the
||| function is used only at its user's types, and its constraint, which
||| then repeats its user's, goes too.
module Primed

%default total

interface Sized a where
  size : a -> Nat

-- Used only at its user's `a`: `twice : a -> Nat` once unprimed.
export
total2 : Sized a => a -> a -> Nat
total2 x y = twice x + twice y
  where
    twice : Sized a' => a' -> Nat
    twice x = size x + size x

-- Used at its user's `a` and at its `b`: stays general, as it does not
-- check at `a` alone.
export
both : Sized a => Sized b => a -> b -> Nat
both x y = one x + one y
  where
    one : Sized a' => a' -> Nat
    one x = size x
