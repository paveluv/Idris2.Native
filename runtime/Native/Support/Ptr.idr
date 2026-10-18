||| Foreign pointers (`Ptr a`, `AnyPtr`), as ordinary code holds them: a
||| `PTR` object, whose one word is the address, which the collector never
||| follows. `Ptr a` and `AnyPtr` are one representation, since the prelude
||| turns one into the other by `believe_me` (`prim__forgetPtr`); the null
||| pointer is the object of the word 0. The memory a pointer addresses is
||| the system's, outside the heap, read through the core
||| (`Memory.foreignBytes`).
module Native.Support.Ptr

import Native.Support.Obj

import Native.Flat.Uniform as Flat
import Native.HeapObj.Shape as HeapObj
import Native.Runtime.Heap as Runtime
import Native.Runtime.Raw as Runtime
import Native.Runtime.Space
import Native.Types.Header
import Native.Types.Kind

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| A new pointer of the word, as ordinary code holds it.
export %inline
newPtr : (word : Bits64) -> Runtime.Heap.Op Runtime.Heap (Flat.Uniform a)
newPtr word = do
  a <- Runtime.Space.allocate 16
  let p = Obj.objectAt {k = Types.Kind.PTR} a
  Obj.store64 p 0 (Types.Header.fixedWord Types.Kind.PTR)
  Obj.store64 p 8 word
  Obj.objectValue p

||| The word a pointer holds: its address, 0 for the null pointer.
export %inline
ptrWord : Flat.Uniform a -> Runtime.Heap.Op Runtime.Heap Bits64
ptrWord v = do
  p <- Obj.valueObject {k = Types.Kind.PTR} v
  Obj.load64 p 8
