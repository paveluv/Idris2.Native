||| The runtime's routines that generated code calls (`Routine`).
|||
||| This module is the contract for them, and the only place it is stated:
||| which routines there are, and each one's arrow (`port`). The runtime
||| declares the function that is each routine by its port (`allocSlow :
||| PortTy (port AllocSlow)` in `Native.Runtime.Space`), which
||| Idris checks where the function is defined; the code generator finds
||| each by that type alone, takes the registers of its calls from the port,
||| and compiles its flat form into the program.
|||
||| Part of the contract between compiled code and the runtime, with the
||| heap-object model (`HeapObj.Shape` says what it is).
module Native.Routine

import Native.Carrier
import Native.Mach
import Native.Port

import Data.List.Elem

%default total

||| The routines of the runtime's core.
public export
data Routine
  = ||| `idris_start`: the stack pointer at entry and the allocation window's
    ||| bytes; the program's start-up, before `main`.
    Start
  | ||| `idris_alloc_slow`: the bytes of an object the window has no room for;
    ||| room for it, after a collection if one is due: a byte address, as
    ||| the window's pointer is on the fast path, since no object is there
    ||| yet.
    AllocSlow
  | ||| `idris_alloc_mutable`: the bytes of an object that will be written
    ||| after it is made; room for it.
    AllocMutable
  | ||| `idris_crash`: a message's address and bytes, written to the standard
    ||| error before the process ends with status 1.
    Crash

||| Each routine's arrow: what its arguments and its result carry.
public export
port : Routine -> Port
port Start = Carrier.ByteAddr ~> Mach.U64 ~> ()
port AllocSlow = Mach.U64 ~> Carrier.ByteAddr
port AllocMutable = Mach.U64 ~> Carrier.ByteAddr
port Crash = Carrier.ByteAddr ~> Mach.U64 ~> ()

||| Every routine, once. The code generator pairs this list's term, as the
||| loaded runtime's context holds it, with its own copy, element by element.
public export
allRoutines : List Routine
allRoutines = [Start, AllocSlow, AllocMutable, Crash]

||| The list holds every routine.
complete : (r : Routine) -> Elem r Routine.allRoutines
complete Start = %search
complete AllocSlow = %search
complete AllocMutable = %search
complete Crash = %search
