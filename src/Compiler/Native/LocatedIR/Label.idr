||| A block's name within its function (`Label`).
|||
||| Part of the located IR (`Compiler.Native.LocatedIR.Program` says what it
||| is).
module Compiler.Native.LocatedIR.Label

%default total

||| A block's name within its function.
public export
Label : Type
Label = Nat
