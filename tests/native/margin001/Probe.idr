-- Whether the allocation margin past the limit is committed, looked at
-- from inside flat code. Generated code may bump the allocation pointer
-- past the limit by up to the margin before it checks, so the runtime
-- keeps that much memory committed past the limit whenever generated code
-- runs: after start-up, after every collection and every growth of the
-- heap, and after a primitive's own allocation in the middle of a window.
--
-- `marginHolds` reads the limit and the end of the committed memory from
-- the runtime's state, and stores a word at the margin's last word past the
-- limit and reads it back: memory past the committed end is reserved but
-- not accessible, and a store there would fault. Nothing lives past the
-- limit, so the store overwrites nothing.
module Probe

import Native.AllocationMargin
import Native.Carrier
import Native.Field
import Native.Flat.Uniform
import Native.Mach
import Native.Runtime.ByteAddr
import Native.Runtime.Cell
import Native.Runtime.Memory
import Native.Runtime.Ordo
import Native.Runtime.PortTy
import Native.Runtime.State
import Native.Support.Obj
import Native.Support.String.Utf8
import Native.Types.Header
import Native.Types.Kind

-- this module's `do` is the runtime's, over the token
%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

||| Whether the margin past the limit is committed, and a word stored at
||| its end reads back.
look : Op Ordo Bool
look = do
  lim <- allocationLimit
  committed <- get "fromCommitted"
  if committed < ByteAddr.offset lim allocationMargin then pure False else do
    storeAt lim (allocationMargin - 8) 4242
    v <- loadAt lim (allocationMargin - 8)
    pure (v == 4242)

%cg native flat Probe.marginHolds
||| 1 if the margin past the limit is committed, else 0; the argument is
||| only the place the caller looks from.
export
marginHolds : Bits64 -> Bits64
marginHolds _ = let (MkOrdo # ok) = look MkOrdo in if ok then 1 else 0

||| The margin looked at after a primitive allocates: `fastConcat`, the
||| runtime's implementation of the Prelude's, joins the pieces into one
||| string, which the runtime allocates itself, growing the heap when the
||| window is out, since a primitive never collects.
lookAfterJoin : Uniform (List String) -> Op Ordo Bool
lookAfterJoin xs = do
  big <- stringObject (fastConcat xs)
  _ <- Obj.header big
  look

%cg native flat Probe.marginHoldsAfterJoin
||| 1 if the margin past the limit is committed after the primitive, else 0.
export
marginHoldsAfterJoin : Uniform (List String) -> Bits64
marginHoldsAfterJoin xs = let (MkOrdo # ok) = lookAfterJoin xs MkOrdo in if ok then 1 else 0
