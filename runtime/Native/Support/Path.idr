||| A path as the system takes one (`withSystemPath`): its bytes, zero-ended,
||| in memory outside the heap (`Runtime.Alloc.Block`), where a string's
||| bytes are not, and with no zero byte after them. A path is copied for
||| the call that takes it and freed after.
|||
||| A path comes as bytes and a count, so that this module reads no string:
||| the string module (`Support.String.Utf8`) gives them.
module Native.Support.Path

import Native.Failure
import Native.Runtime.Alloc.Block
import Native.Runtime.Memory
import Native.Runtime.Ordo as Runtime
import Native.Runtime.Raw
import Native.Runtime.State

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| `use` of the `len` bytes at the address as a path: copied into a new
||| block outside the heap with a zero byte after them, the block freed
||| once `use` is done with it; `none`, with the runtime's last failure
||| that there is no memory, if there is none for the block. The system
||| reads a path up to its first zero byte, so one inside the bytes ends it
||| there, as the C library's callers find.
export %inline covering
withSystemPath : (bytes : Raw) -> (len : Bits64) -> (none : Runtime.Ordo.Op Runtime.Ordo a) ->
                 (use : Raw -> Runtime.Ordo.Op Runtime.Ordo a) -> Runtime.Ordo.Op Runtime.Ordo a
withSystemPath bytes len none use =
  Runtime.Alloc.Block.allocate (len + 1)
    (do Runtime.State.setState Runtime.State.lastFailure (Failure.code Failure.NoMemory)
        none)
    (\b => do
      let MkAddressed p b' = Runtime.Alloc.Block.address b
      Runtime.Memory.copyRaw bytes p len
      Runtime.Memory.storeByteAt p len 0
      r <- use p
      Runtime.Alloc.Block.free b'
      Runtime.Ordo.pure r)
