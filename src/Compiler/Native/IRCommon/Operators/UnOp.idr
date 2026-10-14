||| The unary integer operations of the IRs (`UnOp`).
|||
||| Part of the vocabulary the native backend's two IRs share
||| (`Compiler.Native.IRCommon.Ty` says what it is).
module Compiler.Native.IRCommon.Operators.UnOp

%default total

||| `Negate` is two's-complement negation; `Complement` flips every bit.
public export
data UnOp = Negate | Complement
