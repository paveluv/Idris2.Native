||| Helpers that `scope-helpers` moves into the `where` block of the one
||| function using them. The comments between the cases are about the case,
||| and stay where they are; those directly above a helper are its own, and
||| move with it.
module Moves

import Data.Vect

%default total

-- A user with no `where` block gets one, two columns in from its clause,
-- and the helper goes four in, its documentation with it.

||| Twice a number.
double : Nat -> Nat
double n = n + n

export
quadruple : Nat -> Nat
quadruple n = double (double n)

-- A user with a `where` block already: the helper goes in before the first
-- of the block's functions that uses it, since a block, like a module,
-- defines a name before its use.

square : Nat -> Nat
square n = n * n

export
sumOfSquares : Nat -> Nat -> Nat
sumOfSquares a b = both a b
  where
    both : Nat -> Nat -> Nat
    both x y = square x + square y

-- A chain: `inc` is used only by `incTwice`, and `incTwice` only by
-- `incFour`. `inc` goes first, into `incTwice`'s block, and `incTwice`
-- then takes its block with it into `incFour`'s.

inc : Nat -> Nat
inc = S

incTwice : Nat -> Nat
incTwice n = inc (inc n)

export
incFour : Nat -> Nat
incFour n = incTwice (incTwice n)

-- A type variable the user's type binds too: in the user's block `a` is
-- the user's `a`, one type, and `pairUp y` would not check, so the
-- helper's own is renamed where it is free, to `a'`, and the helper stays
-- generic.

-- the same value, twice
pairUp : a -> (a, a)
pairUp x = (x, x)

export
twins : (a, b) -> ((a, a), (b, b))
twins (x, y) = (pairUp x, pairUp y)

-- A helper whose type binds `{n : Nat}`, which its user's binds too: in
-- the user's block Idris would confuse the two, so the helper's binder is
-- renamed, `n'`, with what refers to it, and the user's call that names
-- it, `{n}` for `{n = n}`, names the new one: `{n' = n}`. Its `e`, a
-- variable the user's type binds too, is renamed as `a` is above.

lengthOf : {n : Nat} -> Vect n e -> Nat
lengthOf _ = n

export
longer : {n : Nat} -> Vect n e -> Nat -> Bool
longer v m = lengthOf {n} v > m

-- A helper in a block of implicit parameters, all it is in the block: the
-- block's header goes, and the helper takes the parameters in its own
-- type. Its calls pass no implicit, so they stay as they are.

parameters {0 t : Type}
  twice : (t -> t) -> t -> t
  twice f = f . f

export
plusFour : Nat -> Nat
plusFour = twice (twice S)
