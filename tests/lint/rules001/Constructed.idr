||| Records and their constructors: `Point`'s is `MkPoint`, named after it;
||| `Pair'`'s is `Two`, reported (`record-constructor`); `Origin` names none,
||| and Idris names it `MkOrigin`.
module Constructed

%default total

||| A point.
public export
record Point where
  constructor MkPoint
  x : Nat

||| Two numbers.
public export
record Pair' where
  constructor Two
  first : Nat
  second : Nat

||| The origin.
public export
record Origin where
  at : Nat
