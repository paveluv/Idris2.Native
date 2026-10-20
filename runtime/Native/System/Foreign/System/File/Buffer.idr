||| The foreign functions of `base`'s `System.File.Buffer`, as the system
||| tier implements them: a buffer's bytes read from a file and written to
||| one (`Native.System.File`), each an ordinary function of the foreign
||| one's name and type (`Native.System` says how they are bound).
module Native.System.Foreign.System.File.Buffer

import Data.Buffer
import Native.Flat.Uniform as Flat
import Native.System.Call
import Native.System.File

%default total

||| `readBufferData`: at most `max` of the file's bytes read into the
||| buffer from the offset, as many as there are before its end or a read
||| that fails; how many, -1 for a closed file. The program ends for bytes
||| outside the buffer.
export covering
prim__readBufferData : AnyPtr -> Buffer -> (offset, max : Int) -> PrimIO Int
prim__readBufferData p b offset max = toPrim $ File.withFile p (-1) (\slot, f => do
  (f', n) <- File.readInto f b offset max
  File.keep slot f'
  pure n)

||| `writeBufferData`: `size` of the buffer's bytes from the offset written
||| to the file; how many, all of them or 0 if a write failed, the file
||| then marked as failed. The program ends for bytes outside the buffer.
export covering
prim__writeBufferData : AnyPtr -> Buffer -> (offset, size : Int) -> PrimIO Int
prim__writeBufferData p b offset size = toPrim $ File.withFile p 0 (\slot, f => do
  ok <- Call.writeFrom f.handle (MkUniform b) offset size
  if ok then pure size else do
    File.keep slot ({ failed := True } f)
    pure 0)
