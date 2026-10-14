||| A block's name within its function (`BlockLabel`).
|||
||| Part of the located IR (`Compiler.Native.LocatedIR.Program` says what it
||| is).
module Compiler.Native.LocatedIR.BlockLabel

%default total

||| A block's name within its function.
public export
BlockLabel : Type
BlockLabel = Nat
