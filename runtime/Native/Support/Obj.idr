||| Objects by their kind (`Obj`): the support tier's addresses. The core
||| knows an object by its shape only (`Memory.Addr`); the support tier,
||| which implements the built-in types, knows the kind too, so that a
||| string's address is not taken for a list cell's. An `Obj k` is an
||| address of the kind's shape, with the kind; only this module makes one,
||| from the core's conversions, and its accesses are the core's, through
||| the address.
module Native.Support.Obj

-- lint: allow public-import: the flat translation reaches through this module
-- (checking an importer's flat functions, it reaches the inline wrappers'
-- bodies, which use the core's accesses, so it is loaded wherever this
-- module is)
import public Native.Runtime.Memory

import Native.Flat.Uniform as Flat
import Native.Heap
import Native.HeapObj.Shape as HeapObj
import Native.Types.Kind as Types

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| The address of an object of the kind `k`: an address of the kind's
||| shape.
export
data Obj : (0 k : Types.Kind) -> Type where
  MkObj : {0 s : HeapObj.Shape} -> (0 shaped : Types.Kind.shapeOf k = Just s) -> Runtime.Memory.Addr s -> Obj k

||| The word, or 32, 16 or 8 bits of it, at the object plus the offset.
export %inline
load64, load32, load16, load8 : Obj k -> (offset : Bits64) -> Heap.Op Heap Bits64
load64 (MkObj _ a) = Runtime.Memory.load64 a
load32 (MkObj _ a) = Runtime.Memory.load32 a
load16 (MkObj _ a) = Runtime.Memory.load16 a
load8 (MkObj _ a) = Runtime.Memory.load8 a

||| Store the word, or its low 32, 16 or 8 bits, at the object plus the
||| offset.
export %inline
store64, store32, store16, store8 : Obj k -> (offset, value : Bits64) -> Heap.Op Heap ()
store64 (MkObj _ a) = Runtime.Memory.store64 a
store32 (MkObj _ a) = Runtime.Memory.store32 a
store16 (MkObj _ a) = Runtime.Memory.store16 a
store8 (MkObj _ a) = Runtime.Memory.store8 a

||| The object at an address the allocator gave as a word.
export %inline
fromWord : {auto 0 shaped : Types.Kind.shapeOf k = Just s} -> Bits64 -> Obj k
fromWord w = MkObj shaped (Runtime.Memory.fromWord w)

||| The word an object's address is.
export %inline
toWord : Obj k -> Bits64
toWord (MkObj _ a) = Runtime.Memory.toWord a

||| The object a value is, and the value an object is, for a type whose
||| values ordinary code holds as objects of the kind always.
export %inline
valueObject : {auto 0 shaped : Types.Kind.shapeOf k = Just s} -> Flat.Uniform a -> Heap.Op Heap (Obj k)
valueObject v = do
  a <- Runtime.Memory.valueObject v
  Heap.pure (MkObj shaped a)

export %inline
objectValue : Obj k -> Heap.Op Heap (Flat.Uniform a)
objectValue (MkObj _ a) = Runtime.Memory.objectValue a

||| The object a pointer word in a field points to, and the pointer word of
||| an object, to store in a field.
export %inline
fieldObject : {auto 0 shaped : Types.Kind.shapeOf k = Just s} -> (word : Bits64) -> Heap.Op Heap (Obj k)
fieldObject w = do
  a <- Runtime.Memory.fieldObject w
  Heap.pure (MkObj shaped a)

export %inline
fieldPointer : Obj k -> Heap.Op Heap Bits64
fieldPointer (MkObj _ a) = Runtime.Memory.fieldPointer a
