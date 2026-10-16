||| The runtime's routines that generated code calls (`Routines`), and those
||| of the string encoding's module (`StringRoutines`): a record of fields,
||| one for each routine, its port the field's type.
|||
||| The runtime gives one record of each, of its functions
||| (`Native.Runtime.routines`, and `strings` in the string encoding's
||| module): every field is required, and each function is checked against
||| its port where the runtime is built. The code generator reads the
||| runtime's record, field by field, for the function that implements
||| each routine, and the registers of its calls from the port.
|||
||| Part of the contract between compiled code and the runtime, with the
||| heap-object model (`HeapObj.Shape` says what it is).
module Native.Routines

import Native.Port

%default total

||| The routines of the generic runtime.
public export
record Routines (f : Port -> Type) where
  constructor MkRoutines
  ||| `idris_start`: the stack pointer at entry and the allocation window's
  ||| bytes; the program's start-up, before `main`.
  start : f (MkPort [Port.Raw, Port.Word] Nothing)
  ||| `idris_alloc_slow`: the bytes of an object the window has no room for;
  ||| its space, after a collection if one is due.
  allocSlow : f (MkPort [Port.Word] (Just Port.Address))
  ||| `idris_alloc_mutable`: the bytes of an object that will be written
  ||| after it is made; its space.
  allocMutable : f (MkPort [Port.Word] (Just Port.Address))
  ||| `idris_crash`: a message's address and bytes, written to the standard
  ||| error before the process ends with status 1.
  crash : f (MkPort [Port.Raw, Port.Word] Nothing)

||| Each routine's entries of two records made one.
public export
zipRoutines : ({p : Port} -> f p -> g p -> h p) -> Routines f -> Routines g -> Routines h
zipRoutines z a b =
  MkRoutines (z a.start b.start) (z a.allocSlow b.allocSlow) (z a.allocMutable b.allocMutable) (z a.crash b.crash)

||| The routines' entries, each with its port.
public export
routineList : Routines f -> List (p : Port ** f p)
routineList r = [(_ ** r.start), (_ ** r.allocSlow), (_ ** r.allocMutable), (_ ** r.crash)]
