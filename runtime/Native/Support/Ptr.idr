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
import Native.Runtime.Ordo as Runtime
import Native.Types.Kind
import Native.Types.Represents

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| A new pointer of the word, as ordinary code holds it.
export %inline
newPtr : {auto 0 rep : Represents Types.Kind.PTR a} -> (word : Bits64) -> Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform a)
newPtr word = do
  p <- Obj.allocate Types.Kind.PTR 0
  Obj.store64 p 8 word
  Obj.objectValue p

||| The word a pointer holds: its address, 0 for the null pointer.
export %inline
ptrWord : {auto 0 only : Only Types.Kind.PTR a} -> Flat.Uniform a -> Runtime.Ordo.Op Runtime.Ordo Bits64
ptrWord v = do
  p <- Obj.valueObject {k = Types.Kind.PTR} v
  Obj.load64 p 8
