||| Where the located IR keeps a value (`Location`): a slot, or one of the
||| target's allocatable registers, each with the type of the value it
||| holds.
|||
||| Part of the located IR (`Native.Codegen.LocatedIR.Program` says what it
||| is).
module Native.Codegen.LocatedIR.Location

import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Codegen.RegDesc
import Native.Rep
import Native.Types.Enc as Types

%default total

||| A location, with the type of the value it holds, which travels with every
||| occurrence, because the rendering reads it: to tell the GC-visible
||| members of a `live` list from the raw ones, among others.
|||
||| A slot is word n of the function's slots, which behave as registers: a
||| value spilled there lives there, as a C compiler's spilled values live
||| in its stack frame. A `Direct` function's slots are its frame on the
||| machine stack, so a direct call keeps its caller's. A CPS function's
||| are the per-thread `SCRATCH` area, one fixed area per thread rather than
||| one per frame, which works because nothing in it survives a CPS
||| transfer: `SCRATCH` is dead across every call, tail call and return. A
||| value needed after a call is in that call's `live` list, and the
||| rendering keeps it elsewhere until the call is over; so the collector
||| never scans the slots.
|||
||| A register is named by its index among the allocatable registers of the
||| value's class in the target's description (`RegDesc`): a word register
||| for a value of the word class, a floating-point one for an `F64`. A
||| register the target keeps for itself has no index.
public export
data Location : Types.Enc -> Type where
  Slot : (n : Nat) -> IRCommon.Ty enc -> Location enc
  Register : (index : Nat) -> IRCommon.Ty enc -> Location enc

public export
Show (Location enc) where
  show (Slot n t) = "slot" ++ show n ++ ":" ++ show t
  show (Register i t) = "reg" ++ show i ++ ":" ++ show t

public export
ty : Location enc -> IRCommon.Ty enc
ty (Slot _ t) = t
ty (Register _ t) = t

||| A slot's number; a register has none.
||| Whether two locations are one place: the same slot, or the same
||| register of a class.
public export
samePlace : Location enc -> Location enc -> Bool
samePlace (Slot n _) (Slot m _) = n == m
samePlace (Register i t) (Register j u) = i == j && IRCommon.Ty.class t == IRCommon.Ty.class u
samePlace _ _ = False

public export
slotNumber : Location enc -> Maybe Nat
slotNumber (Slot n _) = Just n
slotNumber (Register _ _) = Nothing

||| A location's number among a function's, in the target's description: a
||| register's index, the floating-point ones after the word ones, and a
||| slot's after every register, so that the set of a function of few slots
||| is one word.
public export
key : RegDesc -> Location enc -> Nat
key rd (Register i t) = case IRCommon.Ty.class t of
  Rep.WordClass => i
  Rep.FloatClass => rd.wordCount + i
key rd (Slot n _) = rd.wordCount + rd.floatCount + n
