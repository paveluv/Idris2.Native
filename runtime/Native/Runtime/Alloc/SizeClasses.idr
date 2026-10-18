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
  n <- field a w
  setField a w (if up then n + 1 else n - 1)

||| Whether a slab has no block to hand out: none given back, and no room
||| for another past its bump.
noRoom : Config -> (freeList, bump, size, end : Bits64) -> Bool
noRoom _ fl b size end = fl == 0 && b + size > end

export covering
Pages h => Chunks h c => Allocator h (SizeClasses c) where
  allocate s bytes = do
    let cf = s.config
        a = s.arena
    if bytes <= smallBytes cf
      then do
        let k = classOf cf bytes
        first <- field a (availHead cf k)
        g <- if first /= 0 then Ordo.pure first else newSlab s k
        if g == 0 then Ordo.pure 0 else takeBlock cf a (g - 1) k
      else do
        let o = chunkOrder cf bytes
        if o > maxOrder cf then Ordo.pure 0 else do
          addr <- takeChunk s.chunks o
          if addr == 0 then Ordo.pure 0 else do
            g <- granuleOf cf a addr
            setEntry a g kind largeKind
            setEntry a g order o
            markInside a g 1 (1 `shiftL` o)
            Ordo.pure addr
    where
      ||| The entries of a chunk's granules after its head marked as inside it.
      covering
      markInside : (arena, head, i, count : Bits64) -> Ordo.Op h ()
      markInside a g i n =
        if i >= n then Ordo.pure () else do
          setEntry a (g + i) kind insideKind
          setEntry a (g + i) order g
          markInside a g (i + 1) n

      ||| A new slab of the class, empty, first in the class's list: its granule
      ||| plus one, 0 if there is no memory for it.
      covering
      newSlab : SizeClasses c -> (cls : Bits64) -> Ordo.Op h Bits64
      newSlab s k = do
        let cf = s.config
            a = s.arena
            o = slabOrder cf k
        addr <- takeChunk s.chunks o
        if addr == 0 then Ordo.pure 0 else do
          g <- granuleOf cf a addr
          setEntry a g kind slabKind
          setEntry a g order o
          setEntry a g cls k
          setEntry a g freeList 0
          setEntry a g bump addr
          setEntry a g used 0
          markInside a g 1 (1 `shiftL` o)
          push a (availHead cf k) g
          bumpCount a (slabCount cf k) True
          bumpCount a (emptyCount cf k) True
          Ordo.pure (g + 1)

      ||| A block of the slab at the granule, of class `k`: one given back if
      ||| there is one, else the next never used. A slab left with no block to
      ||| hand out leaves its class's list.
      takeBlock : Config -> (arena, granule, cls : Bits64) -> Ordo.Op h Bits64
      takeBlock cf a g k = do
        base <- granuleAddress cf a g
        o <- entry a g order
        fl <- entry a g freeList
        b <- entry a g bump
        u <- entry a g used
        let size = classBytes cf k
            end = base + chunkBytes cf o
        block <- if fl /= 0
          then do
            n <- load fl 0
            setEntry a g freeList n
            Ordo.pure fl
          else do
            setEntry a g bump (b + size)
            Ordo.pure b
        setEntry a g used (u + 1)
        if u == 0 then bumpCount a (emptyCount cf k) False else Ordo.pure ()
        fl' <- entry a g freeList
        b' <- entry a g bump
        if noRoom cf fl' b' size end then remove a (availHead cf k) g else Ordo.pure ()
        Ordo.pure block
  free s addr =
    if addr == 0 then Ordo.pure () else do
      let cf = s.config
          a = s.arena
      ours <- owns a addr
      if not ours then notGiven else do
        g0 <- granuleOf cf a addr
        k0 <- entry a g0 kind
        g <- if k0 == insideKind then entry a g0 order else Ordo.pure g0
        k <- entry a g kind
        if k == slabKind then giveBlock s g addr else
          if k /= largeKind then notGiven else do
            base <- granuleAddress cf a g
            o <- entry a g order
            if addr /= base then notGiven else giveChunk s.chunks o addr
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
        base <- granuleAddress cf a g
        o <- entry a g order
        k <- entry a g cls
        fl <- entry a g freeList
        b <- entry a g bump
        u <- entry a g used
        let size = classBytes cf k
            end = base + chunkBytes cf o
        if u == 0 || addr >= b || (addr - base) `mod` size /= 0 then notGiven else do
          if noRoom cf fl b size end then push a (availHead cf k) g else Ordo.pure ()
          store addr 0 fl
          setEntry a g freeList addr
          setEntry a g used (u - 1)
          if u /= 1 then Ordo.pure () else do
            bumpCount a (emptyCount cf k) True
            e <- field a (emptyCount cf k)
            n <- field a (slabCount cf k)
            if not (quarter cf e n) then Ordo.pure () else do
              remove a (availHead cf k) g
              bumpCount a (slabCount cf k) False
              bumpCount a (emptyCount cf k) False
              giveChunk s.chunks o base
