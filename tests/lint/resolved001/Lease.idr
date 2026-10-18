||| A module that leaves the allocator's linear blocks: reported, at each
||| place (`sealed-allocator`). A block given up as a word is no longer
||| checked to be freed once, so each place says why that is sound, or is
||| reported; one does (`leased`), and is not. A reason covers one place,
||| the first after it: of two below one (`relet`), the second is reported.
||| A block allocated, used and freed (`scratch`) stays within what the
||| types check, and is not reported; the allocator's own function of words
||| (`raw`) is.
module Lease

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
leaked : (none : Raw) -> Op Ordo Raw
leaked none = Block.allocate 64 (pure none) (\b => Block.releaseBlock b)

export covering
leased : (none : Raw) -> Op Ordo Raw
leased none = Block.allocate 64 (pure none) (\b =>
  -- lint: allow sealed-allocator: the caller frees it, by `returned`
  Block.releaseBlock b)

export covering
relet : Op Ordo ()
relet = Block.allocate 64 (pure ()) (\b => do
  -- lint: allow sealed-allocator: given up here and taken back at once
  a <- Block.releaseBlock b
  Block.free (Block.adoptBlock a))

export covering
returned : Raw -> Op Ordo ()
returned a = Block.free (Block.adoptBlock a)

export covering
raw : Op Ordo Bits64
raw = System.allocateBlock 64
