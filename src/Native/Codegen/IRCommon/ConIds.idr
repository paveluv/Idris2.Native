||| The numbering of the type constructors a program uses as values
||| (`ConIds`).
|||
||| Part of the vocabulary the native backend's two IRs share
||| (`Native.Codegen.IRCommon.Ty` says what it is).
module Native.Codegen.IRCommon.ConIds

import Core.Name

%default total

||| The numbering of the type constructors the program builds or matches
||| as values, by name: each one's constructor id, which its `CON` object's
||| header carries as a data constructor's carries its tag. A value of type
||| `Type` meets only type constructors, so an id may be a data
||| constructor's too. Keyed by the full name, so that code compiled later
||| (a JIT's) can number a type constructor the program has as the program
||| does, and a new one after the program's; the image does not carry it
||| yet.
public export
record ConIds where
  constructor MkConIds
  typeCons : List (Name, Nat)

public export
noConIds : ConIds
noConIds = MkConIds []
