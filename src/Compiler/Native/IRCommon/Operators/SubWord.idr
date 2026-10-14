||| The narrow widths of the IRs' loads, stores and extensions (`SubWord`).
|||
||| Part of the vocabulary the native backend's two IRs share
||| (`Compiler.Native.IRCommon.Ty` says what it is).
module Compiler.Native.IRCommon.Operators.SubWord

%default total

||| The narrow widths of `Ext`, `LoadN` and `StoreN`: 8, 16 and 32 bits.
public export
data SubWord = Sub8 | Sub16 | Sub32

||| A sub-word's width in bytes: the unit of a `LoadN` or `StoreN` index.
public export
subWordBytes : SubWord -> Nat
subWordBytes Sub8 = 1
subWordBytes Sub16 = 2
subWordBytes Sub32 = 4
