||| Foreign pointers (`Ptr a`, `AnyPtr`), as ordinary code holds them. `Ptr
||| a` and `AnyPtr` are one representation, since the prelude turns one into
||| the other by `believe_me` (`prim__forgetPtr`).
|||
||| A pointer is one of two objects (`Pointee`), told apart by its kind:
|||
||| - an address of memory outside the heap: a `PTR` object, whose one word
|||   is the address, which the collector never follows; the null pointer
|||   is the object of the null address. It is what foreign code could read:
|||   `malloc`'s blocks, and the null pointer.
||| - an object of the heap, which the runtime gives where `base` takes a
|||   pointer the runtime made and reads it only through the runtime: a
|||   string where `base` expects a pointer to zero-ended bytes, which it
|||   reads by `getString` and then frees. The collector keeps the object,
|||   as for any value, and nothing frees it.
|||
||| What a pointer is, `base`'s code never asks: it hands each pointer from
||| one foreign function to another, all of them the runtime's. Each one
||| that makes a pointer says which it makes (`newPtr`, `stringPtr`); each
||| one that takes one asks which it is (`pointee`), here and nowhere else.
||| One that goes to foreign code is to be an address. An `AnyPtr` may also
||| be a file the runtime opened (`Support.FileObj`), which `base` takes only
||| as a `FilePtr`, and the functions that take any pointer ask for first.
module Native.Support.Ptr

import Native.Support.Obj

import Native.Flat.Uniform as Flat
import Native.HeapObj.Shape as HeapObj
import Native.Runtime.Memory
import Native.Runtime.Ordo as Runtime
import Native.Runtime.Raw as Runtime
import Native.Types.Header
import Native.Types.Kind
import Native.Types.Represents as Types

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| What a pointer is.
public export
data Pointee : Type where
  ||| An address of memory outside the heap; the null address the null
  ||| pointer.
  Address : (address : Runtime.Raw) -> Pointee
  ||| A string of the heap, given for a pointer to its bytes.
  HeapString : Obj Types.Kind.STRING -> Pointee
  ||| A handle: a number the system tier gives for a value of its own.
  Handle : (number : Bits64) -> Pointee

||| A new pointer of the address, as ordinary code holds it.
export %inline
newPtr : {auto 0 rep : Types.Represents Types.Kind.PTR a} -> (address : Runtime.Raw) ->
         Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform a)
newPtr address = do
  p <- Obj.allocate Types.Kind.PTR Types.Header.noParts
  Obj.store64 p 0 (Runtime.Raw.rawWord address)
  Obj.objectValue p

||| The null pointer.
export %inline
nullPtr : {auto 0 rep : Types.Represents Types.Kind.PTR a} ->
          Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform a)
nullPtr = newPtr Runtime.Raw.null

||| A string given for a pointer to its bytes: the string itself.
export %inline
stringPtr : Flat.Uniform String -> Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform (Ptr String))
stringPtr s = do
  o <- Obj.valueObject {k = Types.Kind.STRING} s
  Obj.objectValue o

||| What a pointer is: a handle, or by its object's kind; the program ends
||| for one of none of them.
export %inline
pointee : {auto 0 objs : Types.Represents.Objects a} -> {auto 0 hs : Types.Represents.Handles a} ->
          {auto 0 str : Types.Represents Types.Kind.STRING a} ->
          {auto 0 adr : Types.Represents Types.Kind.PTR a} ->
          Flat.Uniform a -> Runtime.Ordo.Op Runtime.Ordo Pointee
pointee v = do
  handle <- Obj.valueHandle v
  case handle of
    Just n => Runtime.Ordo.pure (Handle n)
    Nothing => do
      s <- Obj.asKind Types.Kind.STRING v
      case s of
        Just o => Runtime.Ordo.pure (HeapString o)
        Nothing => do
          p <- Obj.asKind Types.Kind.PTR v
          case p of
            Just o => do
              w <- Obj.load64 o 0
              Runtime.Ordo.pure (Address (Runtime.Memory.foreignBytes w))
            Nothing =>
              Runtime.Ordo.crashOp "idris: a pointer that is no address, string or handle"
