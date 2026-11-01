||| What an instruction reads (`Opnd`): a register, an immediate, or a
||| static's address, indexed by the type the instruction reads it as; and
||| an operand of some type (`Arg`), as a list of operands of several types
||| holds them.
|||
||| Part of the located IR (`Native.Codegen.LocatedIR.Program` says what it
||| is).
module Native.Codegen.LocatedIR.Opnd

import Native.Codegen.LocatedIR.Location

import Core.Name
import Native.Codegen.IRCommon.Ty as IRCommon
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
data Opnd : (enc : Types.Enc) -> IRCommon.Ty enc -> Type where
  R : Location enc t -> Opnd enc t
  Imm : Int64 -> Opnd enc t
  ||| The address of a static object, as a value. A static never moves, so
  ||| its address needs no register, no slot and no rooting: the rendering
  ||| loads it where it is used.
  StaticRef : Name -> Opnd enc t

public export
Show (Opnd enc t) where
  show (R r) = show r
  show (Imm i) = "#" ++ show i
  show (StaticRef n) = "@" ++ show n

||| An operand of some type: a call's argument, an object's field.
public export
data Arg : Types.Enc -> Type where
  MkArg : {0 t : IRCommon.Ty enc} -> Opnd enc t -> Arg enc

public export
Show (Arg enc) where
  show (MkArg o) = show o

public export
opRegs : Opnd enc t -> List (Location.Place enc)
opRegs (R r) = [Location.At r]
opRegs (Imm _) = []
opRegs (StaticRef _) = []

||| The registers of the operands, in their order, in front of `rest`.
export
opsRegs : List (Arg enc) -> (rest : List (Location.Place enc)) -> List (Location.Place enc)
opsRegs [] rest = rest
opsRegs (MkArg (R r) :: os) rest = Location.At r :: opsRegs os rest
opsRegs (MkArg (Imm _) :: os) rest = opsRegs os rest
opsRegs (MkArg (StaticRef _) :: os) rest = opsRegs os rest

||| The operand with its register replaced by the step.
export
stepOpnd : Location.Step s enc -> s -> Opnd enc t -> (s, Opnd enc t)
stepOpnd f st (R r) = let (st', r') = f st r in (st', R r')
stepOpnd _ st o = (st, o)

||| The operands with their registers replaced by the step, in their order.
export
stepArgs : Location.Step s enc -> s -> List (Arg enc) -> (s, List (Arg enc))
stepArgs _ st [] = (st, [])
stepArgs f st (MkArg o :: os) =
  let (st1, o') = stepOpnd f st o
      (st2, os') = stepArgs f st1 os
  in (st2, MkArg o' :: os')
