||| A record named after its module, and its constructor named after it.
module Geo.Box

%default total

||| A box.
public export
record Box where
  constructor MkBox
  width : Nat
  height : Nat
