||| What an instruction reads (`Opnd`): a register, an immediate, or a
||| static's address.
|||
||| Part of the located IR (`Native.Codegen.LocatedIR.Program` says what it
||| is).
module Native.Codegen.LocatedIR.Opnd

import Native.Codegen.LocatedIR.Reg

import Core.Name
import Native.Types.Enc as Types

%default total

||| A register, or an immediate: a constant written into the instruction
||| (`Imm`, shown as `#i`). An immediate is allowed wherever the target can
||| encode it or the rendering will materialise it into a register: the IR
||| does not know instruction encodings. Where the instruction expects a
||| `Val` or a `Fix`, the immediate is the integer, and the rendering takes
||| its word from `valWord` in `HeapObj.ValEnc`: `#1` is fixnum 1 and `#0`
||| fixnum 0, which as a `Val` is also the erased value, under every value
||| encoding.
public export
data Opnd : Types.Enc -> Type where
  R : Reg enc -> Opnd enc
  Imm : Int64 -> Opnd enc
  ||| The address of a static object, as a value. A static never moves, so
  ||| its address needs no register, no slot and no rooting: the rendering
  ||| loads it where it is used.
  StaticRef : Name -> Opnd enc

public export
Show (Opnd enc) where
  show (R r) = show r
  show (Imm i) = "#" ++ show i
  show (StaticRef n) = "@" ++ show n

public export
opRegs : Opnd enc -> List (Reg enc)
opRegs (R r) = [r]
opRegs (Imm _) = []
opRegs (StaticRef _) = []

||| The registers of the operands, in their order, in front of `rest`.
export
opsRegs : List (Opnd enc) -> (rest : List (Reg enc)) -> List (Reg enc)
opsRegs [] rest = rest
opsRegs (R r :: os) rest = r :: opsRegs os rest
opsRegs (Imm _ :: os) rest = opsRegs os rest
opsRegs (StaticRef _ :: os) rest = opsRegs os rest
