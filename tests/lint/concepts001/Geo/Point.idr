||| A record and a helper about no type of the module: two concepts.
module Geo.Point

%default total

||| A point: its fields come with it, and so does `norm`, about it.
public export
record Point where
  constructor MkPoint
  x : Nat
  y : Nat

export
norm : Point -> Nat
norm p = p.x + p.y

||| A helper about none of the module's types: a concept of its own.
export
twice : Nat -> Nat
twice n = n + n
