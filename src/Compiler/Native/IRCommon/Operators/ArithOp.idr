||| The integer operations of the IRs (`ArithOp`).
|||
||| Part of the vocabulary the native backend's two IRs share
||| (`Compiler.Native.IRCommon.Ty` says what it is).
module Compiler.Native.IRCommon.Operators.ArithOp

%default total

||| Integer operations, on `W64`s or on `Fix`es (`Arith`). A shift takes its
||| count as the second operand, below the word's width; `Shr` is logical and
||| `Sar` arithmetic. The divisions truncate toward zero; dividing by zero, or
||| the most negative word by −1 with `DivS` or `RemS`, is undefined, so the
||| producer checks for both first.
public export
data ArithOp = Add | Sub | Mul | And | Or | Xor | Shl | Shr | Sar
             | DivS | DivU | RemS | RemU

public export
Show ArithOp where
  show Add = "Add"
  show Sub = "Sub"
  show Mul = "Mul"
  show And = "And"
  show Or = "Or"
  show Xor = "Xor"
  show Shl = "Shl"
  show Shr = "Shr"
  show Sar = "Sar"
  show DivS = "DivS"
  show DivU = "DivU"
  show RemS = "RemS"
  show RemU = "RemU"
