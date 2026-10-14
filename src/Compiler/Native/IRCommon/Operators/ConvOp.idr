||| The conversions of the IRs between raw integers and doubles (`ConvOp`).
|||
||| Part of the vocabulary the native backend's two IRs share
||| (`Compiler.Native.IRCommon.Ty` says what it is).
module Compiler.Native.IRCommon.Operators.ConvOp

%default total

||| Conversions between raw integers and doubles.
public export
data ConvOp
  = ||| A signed `W64` to the `F64` of its value.
    I2F
  | ||| An `F64` to a `W64`, truncated toward zero.
    F2I
  | ||| An `F64`'s 64 bits, reinterpreted as a `W64`.
    FBits
  | ||| A `W64`'s 64 bits, reinterpreted as an `F64`.
    BitsF
