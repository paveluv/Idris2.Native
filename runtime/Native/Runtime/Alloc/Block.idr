||| A block of memory outside the heap that its holder owns (`Block`): the
||| way out of the allocator's modules, which are sealed, and the only one
||| the rest of the runtime takes.
|||
||| A block is linear, as the token is: each one is used exactly once, and
||| Idris checks it. Its holder frees it (`free`), or keeps it to use once
||| more after reading its address (`address`, which gives the block back);
||| a block dropped, freed twice, or freed on one branch and not another
||| does not typecheck. `Block` is exported without its constructor, so no
||| block is made but by `allocate`, and none taken apart but by these.
|||
||| Two functions leave what the types check (`releaseBlock`, `adoptBlock`):
||| a block given up as its address, which something outside the types
||| frees or nothing does, and an address taken for a block. The linter
||| flags each use of them, and of the allocator's own functions, outside
||| the allocator's modules, so that each says why it is sound.
|||
||| What the types do not check is the address once read: it is a raw
||| address like any other, and a use of it after the block is freed is
||| the holder's to avoid.
module Native.Runtime.Alloc.Block

import Native.Runtime.Alloc.System

import Native.Runtime.Memory
import Native.Runtime.Ordo
import Native.Runtime.Raw

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| A block of the process's allocator, owned, by its address: raw memory,
||| as the allocator's words become where they leave it.
export
data Block : Type where
  MkBlock : (address : Raw) -> Block

||| A block's bytes, and the block, still to be used.
public export
data Addressed : Type where
  MkAddressed : (bytes : Raw) -> (1 b : Block) -> Addressed

||| A block of `bytes`, aligned to 16, its contents unspecified, for `use`;
||| `none` if there is no memory for it.
export %inline covering
allocate : (bytes : Bits64) -> (none : Ordo.Op Ordo a) -> (use : (1 b : Block) -> Ordo.Op Ordo a) -> Ordo.Op Ordo a
allocate bytes none use = do
  a <- System.allocateBlock bytes
  if a == 0 then none else use (MkBlock (Memory.foreignBytes a))

||| The block's bytes, and the block back.
export %inline
address : (1 b : Block) -> Addressed
address (MkBlock a) = MkAddressed a (MkBlock a)

||| The block given back to the allocator.
export %inline covering
free : (1 b : Block) -> Ordo.Op Ordo ()
free (MkBlock a) = System.freeBlock (Raw.rawWord a)

||| The block given up, as its address: from here nothing checks that it is
||| freed once, by whatever takes the address, or never.
export %inline
releaseBlock : (1 b : Block) -> Ordo.Op Ordo Raw
releaseBlock (MkBlock a) = Ordo.pure a

||| An address taken for a block the allocator gave: nothing checks that it
||| is one, nor that no one else holds it.
export %inline
adoptBlock : (address : Raw) -> Block
adoptBlock a = MkBlock a
