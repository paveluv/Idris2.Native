||| A memory operand (`Mem`): a base, an index, an offset.
|||
||| Part of the located IR (`Native.Codegen.LocatedIR.Program` says what it
||| is).
module Native.Codegen.LocatedIR.Mem

import Native.Codegen.LocatedIR.Location

import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Types.Enc as Types
import Native.Types.Kind as Types

%default total

||| A memory operand's base: an object pointer, or a byte address; never a
||| `Val`, which may be a fixnum, nor a word, which is no address.
public export
data Base : Types.Enc -> Type where
  AtBytes : Location enc IRCommon.Ty.ByteAddr -> Base enc
  AtPtr : {0 k : Types.Kind} -> Location enc (IRCommon.Ty.PtrTo k) -> Base enc

public export
Show (Base enc) where
  show (AtBytes l) = show l
  show (AtPtr l) = show l

||| The base's location, as a place.
public export
place : Base enc -> Location.Place enc
place (AtBytes l) = Location.At l
place (AtPtr l) = Location.At l

||| The base with its location replaced by the step.
export
stepBase : Location.Step s enc -> s -> Base enc -> (s, Base enc)
stepBase f st (AtBytes l) = let (st', l') = f st l in (st', AtBytes l')
stepBase f st (AtPtr l) = let (st', l') = f st l in (st', AtPtr l')

||| A memory operand: a base register, an optional index register, and a
||| constant byte offset. The base is a `PtrTo k` or a `ByteAddr`, such as an
||| area's address or the allocation pointer, never a `Val`, which may be a
||| fixnum.
||| The index, a `W64`, counts units of the access's width: words for `Load`
||| and `Store`, the sub-word's bytes for `LoadN` and `StoreN`. So element `i`
||| of an `ARRAY` is at `MkMem p (Just i) 8`.
|||
||| Every target addresses a base plus an offset, or a base plus an index
||| scaled by the access's width, in one instruction. A rendering that computes
||| part of an address does so within the instruction, so no address outlives
||| it: an interior pointer never meets a collection.
public export
record Mem (enc : Types.Enc) where
  constructor MkMem
  base : Base enc
  index : Maybe (Location enc IRCommon.Ty.W64)
  offset : Int
