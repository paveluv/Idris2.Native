||| The double operations of the IRs (`FOp`).
|||
||| Part of the vocabulary the native backend's two IRs share
||| (`Compiler.Native.IRCommon.Ty` says what it is).
module Compiler.Native.IRCommon.Operators.FOp

%default total

||| Double arithmetic.
public export
data FOp = FAdd | FSub | FMul | FDiv

public export
Show FOp where
  show FAdd = "FAdd"
  show FSub = "FSub"
  show FMul = "FMul"
  show FDiv = "FDiv"
