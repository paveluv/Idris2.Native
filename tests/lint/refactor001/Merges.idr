||| What `merge-clauses` changes: a function several of whose clauses use a
||| helper only it uses becomes one clause with a `case`, so that
||| `scope-helpers` can then move the helper into its `where` block, which a
||| clause of its own would not hold for the others.
module Merges

import Data.Vect

%default total

public export
data Shape = Circle Nat | Square Nat | Dot

-- One argument matched: the case is on it, named after its type, `shape`.
-- The argument every clause names alike, or leaves `_`, `scale`, stays an
-- argument. Each clause keeps its lines, two columns in.

twice : Nat -> Nat
twice n = n + n

export
size : Nat -> Shape -> Nat
size scale (Circle r) = scale * twice r
size scale (Square s) = scale * twice s
size _ Dot = 0

-- Two arguments matched: the case is on a tuple of them, the second name
-- after the type taken by the first, so primed.

flipped : Bool -> Bool
flipped b = not b

export
nand : Bool -> Bool -> Bool
nand True True = flipped True
nand x y = flipped x || flipped y

-- A clause's own `where` block joins the one clause's, after the case.

showNat : Nat -> String
showNat = show

export
describe : Shape -> String
describe (Circle r) = "circle of " ++ showNat r
describe (Square s) = "square of " ++ showNat s
describe Dot = dot
  where
    dot : String
    dot = "a dot"

-- A `where` block using what its clause's pattern binds, `s`, could not
-- join: in the one clause's block `s` would be bound by nothing.

square : Nat -> Nat
square n = n * n

export
area : Shape -> Nat
area (Circle r) = 3 * square r
area (Square s) = squared
  where
    squared : Nat
    squared = square s
area Dot = 0

-- Arguments whose types depend on each other: as a case on a tuple, the
-- match of `x :: _` no longer tells the first is `S k`, and the case does
-- not cover. Only the type checker knows: the run's check finds it, and
-- the change is undone.

pick : a -> a
pick x = x

export
headOr : (n : Nat) -> Vect n a -> a -> a
headOr (S k) (x :: _) _ = pick x
headOr Z [] d = pick d
