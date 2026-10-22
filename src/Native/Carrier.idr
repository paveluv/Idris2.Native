||| What a register carries across the contract (`Carrier`): the contract's
||| first-order description of a register, as data. The runtime gives each
||| carrier its Idris type (`Native.Runtime.PortTy.Carried`), the code
||| generator its register (`Linkage.Routine.carrierTy`), and each is a
||| reading of the same code.
|||
||| A carrier says what it is in `Rep`'s terms (`rep`), but it does not
||| follow `Rep` case for case: it has a case for a kind of register only
||| once an entry of the contract carries one. No entry carries a code
||| address, so no carrier is one; when one does, `Carrier` gains the case.
|||
||| Part of the contract between compiled code and the runtime, with the
||| heap-object model (`HeapObj.Shape` says what it is).
module Native.Carrier

import Native.Mach
import Native.Rep

%default total

||| What a register carries across the boundary, as the Idris type it is.
public export
data Carrier
  = ||| A value of a machine type, in the register its rep says:
    ||| `Mach.type m`. `M` for machine; a port writes the machine type
    ||| itself (`Mach.U64 ~> ...`), which its arrow takes for its carrier.
    M Mach
  | ||| A value of the type, as ordinary code holds it: `Uniform t`.
    ValueOf Type
  | ||| Any value, as ordinary code holds it: `Uniform a`, for the call's `a`.
    Value
  | ||| The address of memory that holds no object: a run of bytes, a range
    ||| of address space, an area, room for an object not yet made. An
    ||| address, with an address's arithmetic only (`Native.Runtime.ByteAddr`).
    ByteAddr

||| How a register of the carrier holds what it carries.
public export
rep : Carrier -> Rep
rep (M m) = Mach.rep m
rep (ValueOf _) = Rep.Uniform
rep Value = Rep.Uniform
rep ByteAddr = Rep.ByteAddr
