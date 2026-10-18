||| Where an allocator of memory outside the heap takes its chunks from
||| (`Chunks`): a chunk of an order, a power of two of granules aligned to
||| its size, committed and zero; and a chunk given back. The buddy
||| allocator over an arena's region is the one source so far (`Buddy`);
||| another (a region of the program's own, a cache of chunks in front of
||| one) is another instance.
module Native.Runtime.Alloc.Chunks

import Native.Runtime.Alloc.Arena
import Native.Runtime.Alloc.Config
import Native.Runtime.Alloc.Pages

import Native.Runtime.Bits
import Native.Runtime.Ordo

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

public export
interface Chunks (0 h : Type) (0 c : Type) where
  ||| A chunk of the order, committed and zero: its address, 0 if there is
  ||| no memory for it.
  takeChunk : c -> (order : Bits64) -> Ordo.Op h Bits64
  ||| A chunk of the order taken before, given back.
  giveChunk : c -> (order, addr : Bits64) -> Ordo.Op h ()

||| The buddy allocator of an arena: a free list of chunks for each order,
||| through the pagemap. A chunk is taken from the smallest order that has
||| one, split in halves down to the order asked for, each upper half freed
||| at its order; when no order has one, the arena takes a largest chunk
||| from its region. A chunk given back joins its buddy, the other half of
||| the chunk of the next order, while that one is free too. A free chunk's
||| memory is given back to the system, so a chunk taken is committed anew,
||| and zero.
public export
record Buddy where
  constructor MkBuddy
  config : Config
  arena : Bits64

||| A free chunk's head marked at its order, and put in its list.
freeAt : Pages h => Config -> (arena, granule, o : Bits64) -> Ordo.Op h ()
freeAt c a g o = do
  setEntry a g kind freeKind
  setEntry a g order o
  push a (freeHead c o) g

||| The chunk at the granule, of order `o`, joined with its buddy while that
||| is free at the same order, then freed.
covering
join : Pages h => Config -> (arena, granule, o : Bits64) -> Ordo.Op h ()
join c a g o =
  if o >= maxOrder c then freeAt c a g o else do
    let b = g `xor` (1 `shiftL` o)
    bk <- entry a b kind
    bo <- entry a b order
    if bk /= freeKind || bo /= o then freeAt c a g o else do
      remove a (freeHead c o) b
      setEntry a b kind unusedKind
      join c a (if b < g then b else g) (o + 1)
  where
    xor : Bits64 -> Bits64 -> Bits64
    xor = prim__xor_Bits64

export covering
Pages h => Chunks h Buddy where
  takeChunk b o = do
    k <- source b.config b.arena o
    case k of
      Nothing => Ordo.pure 0
      Just k => takeFrom b.config b.arena k o
    where
      ||| The order to take a chunk of order `o` from: the least that has a free
      ||| chunk, or the largest, after the arena took a largest chunk from its
      ||| region; nothing when the region or the memory is out.
      covering
      source : Config -> (arena, o : Bits64) -> Ordo.Op h (Maybe Bits64)
      source c a o = do
        found <- smallestFree c a o
        case found of
          Just k => Ordo.pure (Just k)
          Nothing => do
            fresh <- carve c a
            case fresh of
              Nothing => Ordo.pure Nothing
              Just g => do
                freeAt c a g (maxOrder c)
                Ordo.pure (Just (maxOrder c))
        where
          ||| The least order, from `o` up to the largest, whose list has a chunk.
          covering
          smallestFree : Config -> (arena, o : Bits64) -> Ordo.Op h (Maybe Bits64)
          smallestFree c a o =
            if o > maxOrder c then Ordo.pure Nothing else do
              first <- field a (freeHead c o)
              if first /= 0 then Ordo.pure (Just o) else smallestFree c a (o + 1)

      ||| The first free chunk of order `k`, split down to order `o`, committed:
      ||| its address, 0 if the system has not the memory, the chunk freed again.
      covering
      takeFrom : Config -> (arena, k, o : Bits64) -> Ordo.Op h Bits64
      takeFrom c a k o = do
        first <- field a (freeHead c k)
        let g = first - 1
        remove a (freeHead c k) g
        setEntry a g kind unusedKind
        split c a g k o
        addr <- granuleAddress c a g
        ok <- commit addr (chunkBytes c o)
        if ok then Ordo.pure addr else do
          join c a g o
          Ordo.pure 0
        where
          ||| The chunk at the granule, of order `k`, halved down to order `o`, each
          ||| upper half freed.
          covering
          split : Config -> (arena, granule, k, o : Bits64) -> Ordo.Op h ()
          split c a g k o =
            if k <= o then Ordo.pure () else do
              freeAt c a (g + (1 `shiftL` (k - 1))) (k - 1)
              split c a g (k - 1) o
  giveChunk b o addr = do
    let c = b.config
        a = b.arena
    release addr (chunkBytes c o)
    g <- granuleOf c a addr
    setEntry a g kind unusedKind
    join c a g o
