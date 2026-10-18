||| A module of the support tier that leaves the allocator's linear blocks.
||| In a `prim__` function, which implements one of `base`'s foreign
||| functions, a place that does is reported (`sealed-allocator`) unless it
||| says why it is sound: `prim__leaked` does not, `prim__leased` does. A
||| reason covers one place, the first after it: of two below one
||| (`prim__relet`), the second is reported. Outside a `prim__` function the
||| place is reported as `sealed-boundary`, and a suppression of that is a
||| finding itself (`spilled`); so is the allocator's own function of words
||| (`raw`). A block allocated, used and freed (`scratch`) stays within what
||| the types check, and is not reported.
module Native.Support.Lease

-- lint: allow layering: the runtime's modules come from its installed package, not from among the files
import Native.Runtime.Alloc.Block
import Native.Runtime.Alloc.System
import Native.Runtime.Ordo
import Native.Runtime.Raw

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

export covering
scratch : Op Ordo Bits64
scratch = Block.allocate 64 (pure 0) (\b => do
  let MkAddressed _ b' = Block.address b
  Block.free b'
  pure 1)

export covering
prim__leaked : (none : Raw) -> Op Ordo Raw
prim__leaked none = Block.allocate 64 (pure none) (\b => Block.releaseBlock b)

export covering
prim__leased : (none : Raw) -> Op Ordo Raw
prim__leased none = Block.allocate 64 (pure none) (\b =>
  -- lint: allow sealed-allocator: the caller frees it, by `prim__returned`
  Block.releaseBlock b)

export covering
prim__relet : Op Ordo ()
prim__relet = Block.allocate 64 (pure ()) (\b => do
  -- lint: allow sealed-allocator: given up here and taken back at once
  a <- Block.releaseBlock b
  Block.free (Block.adoptBlock a))

export covering
prim__returned : Raw -> Op Ordo ()
prim__returned a = Block.free (Block.adoptBlock a)

export covering
spilled : (none : Raw) -> Op Ordo Raw
spilled none = Block.allocate 64 (pure none) (\b =>
  -- lint: allow sealed-boundary: a reason does not lift it
  Block.releaseBlock b)

export covering
raw : Op Ordo Bits64
raw = System.allocateBlock 64
