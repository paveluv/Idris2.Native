||| The runtime's allocator of memory outside the heap (`SizeClasses`):
||| blocks of the size classes in slabs, and larger blocks as chunks of
||| their own, over a source of chunks in an arena (`Chunks`).
|||
||| A slab is a chunk of one class's blocks. It hands out its blocks never
||| used first, by a bump through the chunk, then those given back, by a
||| free list through their first words, and counts the blocks in use. A
||| class keeps a list of its slabs with a free block, through the pagemap,
||| and takes a new slab when the list is empty. A slab whose blocks are all
||| given back is empty: a class keeps a few of its empty slabs for its next
||| blocks, and gives the chunk of one back once they are too many
||| (`Config.quarter`). A large block is given back as soon as it is freed.
|||
||| A block is found from its address alone, by the pagemap: `free` takes
||| only an address in the region the arena took, in a slab's chunk with a
||| block in use, at a block's start below its bump, or a large block's
||| start; anything else ends the program, so that a stray or foreign
||| address is not taken in. A block given back twice is caught when its
||| slab has no block in use; otherwise not, as the free list would have to
||| be searched.
module Native.Runtime.Alloc.SizeClasses

import Native.Runtime.Alloc.Allocator
import Native.Runtime.Alloc.Arena
import Native.Runtime.Alloc.Chunks
import Native.Runtime.Alloc.Config
import Native.Runtime.Alloc.Pages

import Native.Runtime.Bits
import Native.Runtime.Ordo

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

public export
record SizeClasses c where
  constructor MkSizeClasses
  config : Config
  arena : Bits64
  chunks : c

||| A count of the control block, raised or lowered by one.
bumpCount : Pages h => (arena, word : Bits64) -> (up : Bool) -> Ordo.Op h ()
bumpCount a w up = do
  n <- Arena.field a w
  Arena.setField a w (if up then n + 1 else n - 1)

||| Whether a slab has no block to hand out: none given back, and no room
||| for another past its bump.
noRoom : Config -> (freeList, bump, size, end : Bits64) -> Bool
noRoom _ fl b size end = fl == 0 && b + size > end

export covering
Pages h => Chunks h c => Allocator h (SizeClasses c) where
  allocate s bytes = do
    let cf = s.config
        a = s.arena
    if bytes <= Config.smallBytes cf
      then do
        let k = Config.classOf cf bytes
        first <- Arena.field a (Arena.availHead cf k)
        g <- if first /= 0 then Ordo.pure first else newSlab s k
        if g == 0 then Ordo.pure 0 else takeBlock cf a (g - 1) k
      else do
        let o = Config.chunkOrder cf bytes
        if o > Config.maxOrder cf then Ordo.pure 0 else do
          addr <- Chunks.takeChunk s.chunks o
          if addr == 0 then Ordo.pure 0 else do
            g <- Arena.granuleOf cf a addr
            Arena.setEntry a g Arena.kind Arena.largeKind
            Arena.setEntry a g Arena.order o
            markInside a g 1 (1 `shiftL` o)
            Ordo.pure addr
    where
      ||| The entries of a chunk's granules after its head marked as inside it.
      covering
      markInside : (arena, head, i, count : Bits64) -> Ordo.Op h ()
      markInside a g i n =
        if i >= n then Ordo.pure () else do
          Arena.setEntry a (g + i) Arena.kind Arena.insideKind
          Arena.setEntry a (g + i) Arena.order g
          markInside a g (i + 1) n

      ||| A new slab of the class, empty, first in the class's list: its granule
      ||| plus one, 0 if there is no memory for it.
      covering
      newSlab : SizeClasses c -> (cls : Bits64) -> Ordo.Op h Bits64
      newSlab s k = do
        let cf = s.config
            a = s.arena
            o = Config.slabOrder cf k
        addr <- Chunks.takeChunk s.chunks o
        if addr == 0 then Ordo.pure 0 else do
          g <- Arena.granuleOf cf a addr
          Arena.setEntry a g Arena.kind Arena.slabKind
          Arena.setEntry a g Arena.order o
          Arena.setEntry a g Arena.cls k
          Arena.setEntry a g Arena.freeList 0
          Arena.setEntry a g Arena.bump addr
          Arena.setEntry a g Arena.used 0
          markInside a g 1 (1 `shiftL` o)
          Arena.push a (Arena.availHead cf k) g
          bumpCount a (Arena.slabCount cf k) True
          bumpCount a (Arena.emptyCount cf k) True
          Ordo.pure (g + 1)

      ||| A block of the slab at the granule, of class `k`: one given back if
      ||| there is one, else the next never used. A slab left with no block to
      ||| hand out leaves its class's list.
      takeBlock : Config -> (arena, granule, cls : Bits64) -> Ordo.Op h Bits64
      takeBlock cf a g k = do
        base <- Arena.granuleAddress cf a g
        o <- Arena.entry a g Arena.order
        fl <- Arena.entry a g Arena.freeList
        b <- Arena.entry a g Arena.bump
        u <- Arena.entry a g Arena.used
        let size = Config.classBytes cf k
            end = base + Config.chunkBytes cf o
        block <- if fl /= 0
          then do
            n <- Pages.load fl 0
            Arena.setEntry a g Arena.freeList n
            Ordo.pure fl
          else do
            Arena.setEntry a g Arena.bump (b + size)
            Ordo.pure b
        Arena.setEntry a g Arena.used (u + 1)
        if u == 0 then bumpCount a (Arena.emptyCount cf k) False else Ordo.pure ()
        fl' <- Arena.entry a g Arena.freeList
        b' <- Arena.entry a g Arena.bump
        if noRoom cf fl' b' size end then Arena.remove a (Arena.availHead cf k) g else Ordo.pure ()
        Ordo.pure block
  free s addr =
    if addr == 0 then Ordo.pure () else do
      let cf = s.config
          a = s.arena
      ours <- Arena.owns a addr
      if not ours then notGiven else do
        g0 <- Arena.granuleOf cf a addr
        k0 <- Arena.entry a g0 Arena.kind
        g <- if k0 == Arena.insideKind then Arena.entry a g0 Arena.order else Ordo.pure g0
        k <- Arena.entry a g Arena.kind
        if k == Arena.slabKind then giveBlock s g addr else
          if k /= Arena.largeKind then notGiven else do
            base <- Arena.granuleAddress cf a g
            o <- Arena.entry a g Arena.order
            if addr /= base then notGiven else Chunks.giveChunk s.chunks o addr
    where
      ||| The end of a `free` of an address the allocator did not give, or gave
      ||| and has back already.
      notGiven : Ordo.Op h ()
      notGiven = Ordo.crashOp "idris: free of an address the allocator did not give"

      ||| A block given back to the slab at the granule, after `free` checked it
      ||| starts a block below the bump. A slab that had no block to hand out
      ||| joins its class's list again; one left empty is counted, and its chunk
      ||| given back when the class has too many empty slabs.
      covering
      giveBlock : SizeClasses c -> (granule, addr : Bits64) -> Ordo.Op h ()
      giveBlock s g addr = do
        let cf = s.config
            a = s.arena
        base <- Arena.granuleAddress cf a g
        o <- Arena.entry a g Arena.order
        k <- Arena.entry a g Arena.cls
        fl <- Arena.entry a g Arena.freeList
        b <- Arena.entry a g Arena.bump
        u <- Arena.entry a g Arena.used
        let size = Config.classBytes cf k
            end = base + Config.chunkBytes cf o
        if u == 0 || addr >= b || (addr - base) `mod` size /= 0 then notGiven else do
          if noRoom cf fl b size end then Arena.push a (Arena.availHead cf k) g else Ordo.pure ()
          Pages.store addr 0 fl
          Arena.setEntry a g Arena.freeList addr
          Arena.setEntry a g Arena.used (u - 1)
          if u /= 1 then Ordo.pure () else do
            bumpCount a (Arena.emptyCount cf k) True
            e <- Arena.field a (Arena.emptyCount cf k)
            n <- Arena.field a (Arena.slabCount cf k)
            if not (Config.quarter cf e n) then Ordo.pure () else do
              Arena.remove a (Arena.availHead cf k) g
              bumpCount a (Arena.slabCount cf k) False
              bumpCount a (Arena.emptyCount cf k) False
              Chunks.giveChunk s.chunks o base
