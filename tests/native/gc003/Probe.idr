-- The runtime's own allocation never collects. A string primitive is
-- handed values that ordinary code holds, which a collection would move
-- under it, so when its allocation finds the window out it grows the heap
-- instead; and when a collection was due, it leaves the window empty, so
-- that the next allocation of generated code takes the slow path, which
-- collects. `Main.idr` shows that collection happening; this module shows
-- the primitive not collecting.
--
-- `probe` looks from inside flat code, where nothing allocates but the
-- primitive: it reads the collection count, makes one string of 256 KiB
-- from a short list of 64 pieces of 4 KiB, far past what a collection waits
-- for (twice the live data, and four windows of 4 KiB at least), and reads
-- the count again and the window. It cannot look from ordinary code: every
-- call there allocates the frame it returns to, and that allocation would
-- be the one that collects, before the second look.
module Probe

-- the runtime's functions use its own bit operations, which it does not
-- re-export; flat code that reaches into them imports those too
import Native.Flat.Uniform
import Native.HeapObj.Shape
import Native.Runtime.Bits
import Native.Runtime.Heap
import Native.Runtime.Memory
import Native.Runtime.Space
import Native.Runtime.State
import Native.Support.Obj
import Native.Support.String.Utf8
import Native.Types.Header
import Native.Types.Kind

-- this module's `do` is the runtime's, over the token
%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

||| The count before and after the primitive, and whether the window it
||| left is empty. `fastConcat` is the runtime's implementation of the
||| Prelude's, called directly, and `stringObject` opens its result, the
||| `Uniform String`, to the object, whose first word is the
||| header with the length in bytes.
look : Uniform (List String) -> Op Heap (Bits64, Bits64, Bool)
look xs = do
  before <- getState collections
  big <- stringObject (fastConcat xs)
  bytes <- Obj.load64 big 0
  during <- getState collections
  hp <- allocationPointer
  lim <- allocationLimit
  pure (before, during, hp == lim && readPart StringBytes bytes == 262144)

%cg native flat Probe.probe
||| The count the next collection will make: the count after the
||| primitive, plus one. 0 if the primitive collected, or left the window
||| unemptied.
export
probe : Uniform (List String) -> Bits64
probe xs = let (MkHeap # (before, during, empty)) = look xs MkHeap in
           if before == during && empty then during + 1 else 0
