||| Two concepts that refer to each other: each would import the other, so
||| `split-module` leaves them together.
module Heap.Ring

%default total

public export
data A = MkA

public export
data B = MkB

export
toB : A -> B
toB MkA = MkB

export
toA : B -> A
toA MkB = MkA
