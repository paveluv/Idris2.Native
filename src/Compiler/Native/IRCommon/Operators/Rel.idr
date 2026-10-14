||| The comparison relations of the IRs (`Rel`).
|||
||| Part of the vocabulary the native backend's two IRs share
||| (`Compiler.Native.IRCommon.Ty` says what it is).
module Compiler.Native.IRCommon.Operators.Rel

%default total

||| Comparison relations on integers; `S` and `U` are signed and unsigned. On
||| `Fix`es a relation compares the fixnums' values, as 64-bit integers; every
||| value encoding with fixnums orders the words as it orders the values, both
||| signed and unsigned, so a rendering compares the words.
public export
data Rel = EqR | NeR | LtS | LeS | GtS | GeS | LtU | LeU | GtU | GeU
