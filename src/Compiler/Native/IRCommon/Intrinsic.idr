||| The intrinsics: operations on machine state that the runtime needs and no
||| instruction expresses (`Intrinsic`).
|||
||| Part of the vocabulary the native backend's two IRs share
||| (`Compiler.Native.IRCommon.Ty` says what it is).
module Compiler.Native.IRCommon.Intrinsic

%default total

||| Operations on machine state that the runtime needs and no instruction
||| expresses. Each is a fixed instruction sequence per target, never a call.
public export
data Intrinsic
  = ||| The allocation pointer, as a `W64`.
    GetHp
  | ||| Set the allocation pointer from one `W64`.
    SetHp
  | ||| The allocation limit, as a `W64`.
    GetHpLim
  | ||| Set the allocation limit from one `W64`.
    SetHpLim
  | ||| The current continuation, as a `PtrTo CONT` (heap lowering).
    GetK
  | ||| Set the current continuation from one `PtrTo CONT`: how the collector
    ||| publishes a continuation it has moved.
    SetK
  | ||| One system call: a number and up to six `W64` arguments, giving a
    ||| `W64`. A collection never starts in a system call.
    Syscall
  | ||| The machine stack pointer, as a `W64`; for start-up only.
    GetStackPointer
  | ||| Set the machine stack pointer from one `W64`; for start-up only.
    SetStackPointer

public export
Show Intrinsic where
  show GetHp = "getHp"
  show SetHp = "setHp"
  show GetHpLim = "getHpLim"
  show SetHpLim = "setHpLim"
  show GetK = "getK"
  show SetK = "setK"
  show Syscall = "syscall"
  show GetStackPointer = "getStackPointer"
  show SetStackPointer = "setStackPointer"
