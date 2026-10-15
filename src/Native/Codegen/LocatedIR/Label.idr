||| A block's name within its function (`Label`).
|||
||| Part of the located IR (`Native.Codegen.LocatedIR.Program` says what it
||| is).
module Native.Codegen.LocatedIR.Label

%default total

||| A block's name within its function.
public export
Label : Type
Label = Nat
