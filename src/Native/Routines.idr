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
||| heap-object model (`HeapObj.Enc` says what it is).
module Native.Routines

import Native.Port

%default total

||| The routines of the generic runtime.
public export
record Routines (f : Port -> Type) where
  constructor MkRoutines
  ||| `idris_start`: the stack pointer at entry and the allocation window's
  ||| bytes; the program's start-up, before `main`.
  start : f (Port.MkPort [Port.Word, Port.Word] Nothing)
  ||| `idris_alloc_slow`: the bytes of an object the window has no room for;
  ||| its space, after a collection if one is due.
  allocSlow : f (Port.MkPort [Port.Word] (Just Port.Address))
  ||| `idris_alloc_mutable`: the bytes of an object that will be written
  ||| after it is made; its space.
  allocMutable : f (Port.MkPort [Port.Word] (Just Port.Address))
  ||| `idris_crash`: a message's address and bytes, written to the standard
  ||| error before the process ends with status 1.
  crash : f (Port.MkPort [Port.Word, Port.Word] Nothing)

||| Each routine's entries of two records made one.
public export
zipRoutines : ({p : Port} -> f p -> g p -> h p) -> Routines f -> Routines g -> Routines h
zipRoutines z a b =
  MkRoutines (z a.start b.start) (z a.allocSlow b.allocSlow) (z a.allocMutable b.allocMutable) (z a.crash b.crash)

||| The routines' entries, each with its port.
public export
routineList : Routines f -> List (p : Port ** f p)
routineList r = [(_ ** r.start), (_ ** r.allocSlow), (_ ** r.allocMutable), (_ ** r.crash)]

||| The primitive operations on strings and their comparison, over strings
||| as ordinary code holds them: a character is its code point, a count or
||| an index a word, an order -1, 0 or 1.
public export
record StringRoutines (f : Port -> Type) where
  constructor MkStringRoutines
  length : f (Port.MkPort [Port.Str] (Just Port.Word))
  head : f (Port.MkPort [Port.Str] (Just Port.Word))
  tail : f (Port.MkPort [Port.Str] (Just Port.Str))
  index : f (Port.MkPort [Port.Str, Port.Word] (Just Port.Word))
  cons : f (Port.MkPort [Port.Word, Port.Str] (Just Port.Str))
  append : f (Port.MkPort [Port.Str, Port.Str] (Just Port.Str))
  reverse : f (Port.MkPort [Port.Str] (Just Port.Str))
  ||| The characters from `start`, `len` of them, both clamped to the string.
  substr : f (Port.MkPort [Port.Signed, Port.Signed, Port.Str] (Just Port.Str))
  compare : f (Port.MkPort [Port.Str, Port.Str] (Just Port.Signed))

||| Each string routine's entries of two records made one.
public export
zipStringRoutines : ({p : Port} -> f p -> g p -> h p) -> StringRoutines f -> StringRoutines g -> StringRoutines h
zipStringRoutines z a b =
  MkStringRoutines (z a.length b.length) (z a.head b.head) (z a.tail b.tail) (z a.index b.index)
    (z a.cons b.cons) (z a.append b.append) (z a.reverse b.reverse) (z a.substr b.substr) (z a.compare b.compare)

||| The string routines' entries, each with its port.
public export
stringRoutineList : StringRoutines f -> List (p : Port ** f p)
stringRoutineList r =
  [(_ ** r.length), (_ ** r.head), (_ ** r.tail), (_ ** r.index), (_ ** r.cons), (_ ** r.append),
   (_ ** r.reverse), (_ ** r.substr), (_ ** r.compare)]
