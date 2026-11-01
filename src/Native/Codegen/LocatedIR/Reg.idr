||| The registers of the located IR (`Reg`): slots of the per-thread `SCRATCH`
||| area, each with the type of the values it holds.
|||
||| Part of the located IR (`Native.Codegen.LocatedIR.Program` says what it
||| is).
module Native.Codegen.LocatedIR.Reg

import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Types.Enc as Types

%default total

||| A register: word n of the function's slots, with the type of the values
||| it holds. The slots behave as registers: every value lives in one, as a
||| C compiler's spilled values live in its stack frame. A `Direct`
||| function's slots are its frame on the machine stack, so a direct call
||| keeps its caller's. A CPS function's are the per-thread `SCRATCH` area,
||| one fixed area per thread rather than one per frame, which works
||| because nothing in it survives a CPS transfer: `SCRATCH` is dead across
||| every call, tail call and return. A value needed after a call is in that
||| call's `live` list, and the rendering keeps it elsewhere until the call
||| is over; so the collector never scans the slots. The type travels with every occurrence, because the rendering
||| reads it, to tell the GC-visible members of a `live` list from the raw
||| ones, among others.
public export
data Reg : Types.Enc -> Type where
  Slot : (n : Nat) -> IRCommon.Ty enc -> Reg enc

public export
Show (Reg enc) where
  show (Slot n t) = "slot" ++ show n ++ ":" ++ show t

public export
ty : Reg enc -> IRCommon.Ty enc
ty (Slot _ t) = t

||| The slot's number: the register's identity.
public export
slot : Reg enc -> Nat
slot (Slot n _) = n
