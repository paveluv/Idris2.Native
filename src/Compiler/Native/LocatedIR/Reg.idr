||| The registers of the located IR (`Reg`): slots of the per-thread `SCRATCH`
||| area, each with the type of the values it holds.
|||
||| Part of the located IR (`Compiler.Native.LocatedIR.Program` says what it
||| is).
module Compiler.Native.LocatedIR.Reg

import Compiler.Native.HeapObject.Enc
import Compiler.Native.IRCommon.Ty

%default total

||| A register: word n of the per-thread `SCRATCH` area, with the type of the
||| values it holds. `SCRATCH` behaves as registers: every value lives in a
||| slot, as a C compiler's spilled values live in its stack frame, but there
||| is one fixed area per thread rather than one per frame. That works
||| because nothing in it survives a call: `SCRATCH` is dead across every
||| call, tail call and return, and every direct call. A value needed after
||| a call is in that call's `live` list, and the rendering keeps it
||| elsewhere until the call is over; so the collector never scans
||| `SCRATCH`. The type travels with every occurrence, because the rendering
||| reads it, to tell the GC-visible members of a `live` list from the raw
||| ones, among others.
public export
data Reg : Enc -> Type where
  Slot : (n : Nat) -> Ty enc -> Reg enc

public export
Show (Reg enc) where
  show (Slot n t) = "slot" ++ show n ++ ":" ++ show t

public export
regTy : Reg enc -> Ty enc
regTy (Slot _ t) = t

||| The slot's number: the register's identity.
public export
slotOf : Reg enc -> Nat
slotOf (Slot n _) = n
