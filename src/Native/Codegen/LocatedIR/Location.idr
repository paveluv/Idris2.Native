||| Where the located IR keeps a value (`Location`): a slot, or one of the
||| target's allocatable registers, indexed by the type of the value it
||| holds; and a location of a value of some type (`Place`), as a list of
||| values of several types holds them.
|||
||| Part of the located IR (`Native.Codegen.LocatedIR.Program` says what it
||| is).
module Native.Codegen.LocatedIR.Location

import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Codegen.RegDesc
import Native.Rep
import Native.Types.Enc as Types

%default total

||| A location of a value of type `t`. The type is its index, so that an
||| instruction states the types of its locations and every pass that makes
||| one is checked against them; and its field too, which travels with every
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
data Location : (enc : Types.Enc) -> IRCommon.Ty enc -> Type where
  Slot : (n : Nat) -> (t : IRCommon.Ty enc) -> Location enc t
  Register : (index : Nat) -> (t : IRCommon.Ty enc) -> Location enc t

public export
Show (Location enc t) where
  show (Slot n t) = "slot" ++ show n ++ ":" ++ show t
  show (Register i t) = "reg" ++ show i ++ ":" ++ show t

||| The type of the value the location holds, its field.
public export
ty : Location enc t -> IRCommon.Ty enc
ty (Slot _ t) = t
ty (Register _ t) = t

||| Whether two locations are one place: the same slot, or the same
||| register of a class.
public export
samePlace : Location enc t -> Location enc u -> Bool
samePlace (Slot n _) (Slot m _) = n == m
samePlace (Register i t) (Register j u) = i == j && IRCommon.Ty.class t == IRCommon.Ty.class u
samePlace _ _ = False

||| A slot's number; a register has none.
public export
slotNumber : Location enc t -> Maybe Nat
slotNumber (Slot n _) = Just n
slotNumber (Register _ _) = Nothing

||| A location's number among a function's, in the target's description: a
||| register's index, the floating-point ones after the word ones, and a
||| slot's after every register, so that the set of a function of few slots
||| is one word.
public export
key : RegDesc -> Location enc t -> Nat
key rd (Register i t) = case IRCommon.Ty.class t of
  Rep.WordClass => i
  Rep.FloatClass => rd.wordCount + i
key rd (Slot n _) = rd.wordCount + rd.floatCount + n

||| A step of a traversal of locations: a state, threaded through them in
||| order, and each location replaced by one of its type.
public export
0 Step : Type -> Types.Enc -> Type
Step s enc = {0 t : IRCommon.Ty enc} -> s -> Location enc t -> (s, Location enc t)

||| The location's register at the index, of its class: where a pass puts
||| the value it holds, at its type.
public export
inRegister : Nat -> Location enc t -> Location enc t
inRegister k (Slot _ t) = Register k t
inRegister k (Register _ t) = Register k t

||| A location of a value of some type: a live list's, a block's parameters.
||| Its type is the location's field.
public export
data Place : Types.Enc -> Type where
  At : {0 t : IRCommon.Ty enc} -> Location enc t -> Place enc

public export
Show (Place enc) where
  show (At l) = show l

||| The places replaced by the step, in their order.
export
stepPlaces : Step s enc -> s -> List (Place enc) -> (s, List (Place enc))
stepPlaces _ st [] = (st, [])
stepPlaces f st (At l :: ps) =
  let (st1, l') = f st l
      (st2, ps') = stepPlaces f st1 ps
  in (st2, At l' :: ps')

namespace Place
  ||| The type of the value the place holds.
  public export
  ty : Place enc -> IRCommon.Ty enc
  ty (At l) = ty l

  ||| Whether two places are one.
  public export
  same : Place enc -> Place enc -> Bool
  same (At l) (At m) = samePlace l m

  ||| A slot's number; a register has none.
  public export
  slotNumber : Place enc -> Maybe Nat
  slotNumber (At l) = slotNumber l

  ||| The place's number among a function's (`Location.key`).
  public export
  key : RegDesc -> Place enc -> Nat
  key rd (At l) = key rd l
