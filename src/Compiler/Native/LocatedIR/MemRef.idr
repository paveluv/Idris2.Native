||| A memory operand (`MemRef`): a base, an index, an offset.
|||
||| Part of the located IR (`Compiler.Native.LocatedIR.Program` says what it
||| is).
module Compiler.Native.LocatedIR.MemRef

import Compiler.Native.HeapObject.Enc
import Compiler.Native.LocatedIR.Reg

%default total

||| A memory operand: a base register, an optional index register, and a
||| constant byte offset. The base is a `PtrTo k` or a `W64`, such as an area's
||| address or the allocation pointer, never a `Val`, which may be a fixnum.
||| The index, a `W64`, counts units of the access's width: words for `Load`
||| and `Store`, the sub-word's bytes for `LoadN` and `StoreN`. So element `i`
||| of an `ARRAY` is at `MkMemRef p (Just i) 8`.
|||
||| Every target addresses a base plus an offset, or a base plus an index
||| scaled by the access's width, in one instruction. A rendering that computes
||| part of an address does so within the instruction, so no address outlives
||| it: an interior pointer never meets a collection.
public export
record MemRef (enc : Enc) where
  constructor MkMemRef
  base : Reg enc
  index : Maybe (Reg enc)
  offset : Int
