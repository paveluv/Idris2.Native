||| A path as the system takes one (`systemPath`): its bytes, zero-ended, in
||| memory outside the heap (`Runtime.Alloc.System`), where a string's bytes
||| are not, and with no zero byte after them. A path is copied for the call
||| that takes it and freed after.
|||
||| A path comes as bytes and a count, so that this module reads no string:
||| the string module (`Support.String.Utf8`) gives them.
module Native.Support.Path

import Native.Failure
import Native.Runtime.Alloc.System
import Native.Runtime.Memory
import Native.Runtime.Ordo as Runtime
import Native.Runtime.Raw
import Native.Runtime.State

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| The `len` bytes at the address copied into a new block outside the heap
||| and a zero byte after them: the block's address, 0 if there is no memory
||| for it. The system reads a path up to its first zero byte, so one inside
||| the bytes ends it there, as the C library's callers find. With no
||| memory, the runtime's last failure is that.
export covering
systemPath : (bytes : Raw) -> (len : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bits64
systemPath bytes len = do
  p <- Runtime.Alloc.System.allocateBlock (len + 1)
  if p == 0
    then do
      Runtime.State.setState Runtime.State.lastFailure (Failure.code Failure.NoMemory)
      Runtime.Ordo.pure 0
    else do
    Runtime.Memory.copyRaw bytes (Runtime.Memory.foreignBytes p) len
    Runtime.Memory.storeByteAt (Runtime.Memory.foreignBytes p) len 0
    Runtime.Ordo.pure p
