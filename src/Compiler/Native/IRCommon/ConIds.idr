||| The link-time numbering of constructors (`ConIds`).
|||
||| Part of the vocabulary the native backend's two IRs share
||| (`Compiler.Native.IRCommon.Ty` says what it is).
module Compiler.Native.IRCommon.ConIds

import Core.Name

%default total

||| The link-time numbering of constructors: data constructors, by (type,
||| constructor), and type constructors used as values, to their global ids,
||| which a `CON` header carries as its constructor id.
public export
record ConIds where
  constructor MkConIds
  dataCons : List ((Name, Name), Nat)
  typeCons : List (Name, Nat)

public export
noConIds : ConIds
noConIds = MkConIds [] []
