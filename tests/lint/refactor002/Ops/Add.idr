||| Addition: one of two modules of one small kind, which `join-modules`
||| makes one, `Ops`.
module Ops.Add

%default total

||| The sum of two numbers.
export
add : Nat -> Nat -> Nat
add = plus
