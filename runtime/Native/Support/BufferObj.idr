||| Buffers of `Data.Buffer` as the runtime keeps them: a `BUFFER` object,
||| its bytes after its header, as many as the header says, zero when it
||| is made, as Chez's are.
|||
||| Every read and write of a buffer is checked to lie inside it
||| (`bytesAt`, `load`, `store`): the program ends for one that does not,
||| as Chez's bytevectors end it, where the C library's would read or write
||| past it. A buffer's words of several bytes are little-endian, the
||| native order of every platform targeted.
module Native.Support.BufferObj

import Native.Support.Obj

-- lint: allow layering: `Buffer` is `base`'s external type, which this
-- module's functions take and make; nothing of `base` runs here
import Data.Buffer
import Native.Flat.Uniform as Flat
import Native.HeapObj.Shape as HeapObj
import Native.Runtime.ByteAddr as Runtime
import Native.Runtime.Memory
import Native.Runtime.Ordo as Runtime
import Native.Types.Header
import Native.Types.Kind
import Native.Types.Repr

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| The buffer's object.
%inline
bufferObject : Flat.Uniform Buffer -> Runtime.Ordo.Op Runtime.Ordo (Obj Types.Kind.BUFFER)
bufferObject = Obj.valueObject

||| The bytes of a buffer's object.
objectSize : Obj Types.Kind.BUFFER -> Runtime.Ordo.Op Runtime.Ordo Bits64
objectSize o = do
  h <- Obj.header o
  Runtime.Ordo.pure (Types.Header.readPart Types.Header.BufferBytes h)

||| A new buffer of `n` bytes, all zero.
export covering
zeroBuffer : (n : Bits64) -> Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform Buffer)
zeroBuffer n = do
  o <- Obj.allocate Types.Kind.BUFFER
    (Types.Header.withPart Types.Header.BufferBytes n Types.Header.noParts)
  Runtime.Memory.fillBytes (Obj.objectBytes o 0) n 0
  Obj.objectValue o

||| The buffer's bytes.
export
size : Flat.Uniform Buffer -> Runtime.Ordo.Op Runtime.Ordo Bits64
size b = do
  o <- bufferObject b
  objectSize o

||| The buffer's object, if its `n` bytes from the offset lie inside it;
||| the end of the program if not.
inside : Flat.Uniform Buffer -> (offset, n : Int) ->
         Runtime.Ordo.Op Runtime.Ordo (Obj Types.Kind.BUFFER)
inside b offset n = do
  o <- bufferObject b
  all <- objectSize o
  if offset < 0 || n < 0 || cast offset > all || cast n > all - cast offset
    then Runtime.Ordo.crashOp "idris: bytes outside a buffer"
    else Runtime.Ordo.pure o

||| The address of the buffer's `n` bytes from the offset, for the system
||| to read or write them, or to copy; the program ends for bytes outside
||| the buffer. An address of the heap, good while the runtime's function
||| runs, as no collection comes before it returns.
export
bytesAt : Flat.Uniform Buffer -> (offset, n : Int) -> Runtime.Ordo.Op Runtime.Ordo Runtime.ByteAddr
bytesAt b offset n = do
  o <- inside b offset n
  Runtime.Ordo.pure (Obj.objectBytes o (cast offset))

||| The `width` bytes, 1, 2, 4 or 8, of the buffer at the offset, as a
||| number, and storing a number's low bytes there; the program ends for
||| bytes outside the buffer.
export
load : (width : Bits64) -> Flat.Uniform Buffer -> (offset : Int) ->
       Runtime.Ordo.Op Runtime.Ordo Bits64
load width b offset = do
  o <- inside b offset (cast width)
  if width == 1 then Obj.load8 o (cast offset)
    else if width == 2 then Obj.load16 o (cast offset)
    else if width == 4 then Obj.load32 o (cast offset)
    else Obj.load64 o (cast offset)

export
store : (width : Bits64) -> Flat.Uniform Buffer -> (offset : Int) -> (value : Bits64) ->
        Runtime.Ordo.Op Runtime.Ordo ()
store width b offset v = do
  o <- inside b offset (cast width)
  if width == 1 then Obj.store8 o (cast offset) v
    else if width == 2 then Obj.store16 o (cast offset) v
    else if width == 4 then Obj.store32 o (cast offset) v
    else Obj.store64 o (cast offset) v
