||| An arena of memory outside the heap: one reservation of address space,
||| which holds the arena's control block, its pagemap, and the region its
||| chunks are cut from, each committed only as it is used.
|||
||| The region is aligned to the largest chunk, so that every chunk is
||| aligned to its size and a chunk's buddy is found by its address alone.
||| The arena takes the region a largest chunk at a time, from its start
||| (`carve`); the region's address space past what it took is never touched.
|||
||| The pagemap has an entry of eight words for every granule of the region,
||| so that the allocator finds what an address belongs to by one load:
|||
|||   word 0   what the granule is (its `kind`): unused, the head of a free
|||            chunk, inside a chunk in use (word 1: the granule of its head),
|||            the head of a slab, or the head of a large block
|||   word 1   a head's order (an `Inside`'s head)
|||   words 2, 3  a head's next and previous in its list, each a granule plus
|||            one, 0 for none: the free chunks of its order, or the slabs of
|||            its class with a free block
|||   words 4..7  a slab's class, its free list, its bump and its blocks in use
|||
||| The control block's words: a mark that it is an arena, the region's
||| start and end, the end of what the arena took of it, the pagemap's
||| address, the end of what is committed of it; then the head of each
||| order's list of free chunks, and for each class the head of its list of
||| slabs with a free block, its slabs, and its empty slabs.
module Native.Runtime.Alloc.Arena

import Native.Runtime.Alloc.Config
import Native.Runtime.Alloc.Pages
import Native.Runtime.Bits
import Native.Runtime.Heap

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

------------------------------------------------------------------------------
-- The control block

||| The words of the control block, by name.
mark, regionStart, regionEnd, taken, pagemap, pagemapCommitted : Bits64
mark = 0
regionStart = 1
regionEnd = 2
taken = 3
pagemap = 4
pagemapCommitted = 5

||| What the control block's first word holds: `ARENA` in ASCII.
arenaMark : Bits64
arenaMark = 0x414E455241

||| Where the free chunks' heads start, one word an order.
freeHeads : Bits64
freeHeads = 8

||| The word of the head of the order's free chunks, and of the class's
||| slabs with a free block, its slabs, and its empty ones.
export
freeHead : Config -> (order : Bits64) -> Bits64
freeHead _ o = freeHeads + o

export
availHead, slabCount, emptyCount : Config -> (cls : Bits64) -> Bits64
availHead c k = freeHeads + maxOrder c + 1 + k
slabCount c k = availHead c k + classCount c
emptyCount c k = slabCount c k + classCount c

||| A word of the control block, and storing one.
export
field : Pages h => (arena, i : Bits64) -> Heap.Op h Bits64
field a i = load a (8 * i)

export
setField : Pages h => (arena, i, value : Bits64) -> Heap.Op h ()
setField a i v = store a (8 * i) v

------------------------------------------------------------------------------
-- The pagemap

||| What a pagemap entry says a granule is.
export
unusedKind, freeKind, insideKind, slabKind, largeKind : Bits64
unusedKind = 0
freeKind = 1
insideKind = 2
slabKind = 3
largeKind = 4

||| The words of an entry, by name.
export
kind, order, next, prev, cls, freeList, bump, used : Bits64
kind = 0
order = 1
next = 2
prev = 3
cls = 4
freeList = 5
bump = 6
used = 7

||| The bytes of a pagemap entry, as their logarithm.
entryShift : Bits64
entryShift = 6

||| Word `i` of the granule's entry, and storing one.
export
entry : Pages h => (arena, granule, i : Bits64) -> Heap.Op h Bits64
entry a g i = do
  p <- field a pagemap
  load (p + (g `shiftL` entryShift)) (8 * i)

export
setEntry : Pages h => (arena, granule, i, value : Bits64) -> Heap.Op h ()
setEntry a g i v = do
  p <- field a pagemap
  store (p + (g `shiftL` entryShift)) (8 * i) v

||| The granule an address of the region is in, and a granule's address.
export
granuleOf : Pages h => Config -> (arena, addr : Bits64) -> Heap.Op h Bits64
granuleOf c a addr = do
  r <- field a regionStart
  Heap.pure ((addr - r) `shiftR` c.granuleShift)

export
granuleAddress : Pages h => Config -> (arena, granule : Bits64) -> Heap.Op h Bits64
granuleAddress c a g = do
  r <- field a regionStart
  Heap.pure (r + (g `shiftL` c.granuleShift))

||| Whether an address is in what the arena took of its region: only there
||| has it ever given memory.
export
owns : Pages h => (arena, addr : Bits64) -> Heap.Op h Bool
owns a addr = do
  r <- field a regionStart
  t <- field a taken
  Heap.pure (r <= addr && addr < t)

------------------------------------------------------------------------------
-- Lists through the pagemap

||| A granule put first in the list whose head is the control block's word.
export
push : Pages h => (arena, headWord, granule : Bits64) -> Heap.Op h ()
push a hw g = do
  first <- field a hw
  setEntry a g next first
  setEntry a g prev 0
  if first == 0 then Heap.pure () else setEntry a (first - 1) prev (g + 1)
  setField a hw (g + 1)

||| A granule taken out of the list whose head is the control block's word.
export
remove : Pages h => (arena, headWord, granule : Bits64) -> Heap.Op h ()
remove a hw g = do
  n <- entry a g next
  p <- entry a g prev
  if p == 0 then setField a hw n else setEntry a (p - 1) next n
  if n == 0 then Heap.pure () else setEntry a (n - 1) prev p

------------------------------------------------------------------------------
-- Making an arena, and taking its region

||| `bytes` rounded up to whole pages.
pages : Pages h => (bytes : Bits64) -> Heap.Op h Bits64
pages n = do
  page <- pageBytes
  Heap.pure ((n + (page - 1)) .&. (0 - page))

||| A new arena of the configuration: its reservation made, its control
||| block committed; its address, 0 if the system has not the address space
||| or the memory.
export
newArena : Pages h => Config -> Heap.Op h Bits64
newArena c = do
  control <- pages (controlBytes c)
  entries <- pages ((1 `shiftL` (c.regionShift - c.granuleShift)) `shiftL` entryShift)
  let region = 1 `shiftL` c.regionShift
      align = 1 `shiftL` c.maxChunkShift
  base <- reserve (control + entries + region + align)
  if base == 0 then Heap.pure 0 else do
    ok <- commit base control
    if not ok then Heap.pure 0 else do
      let start = (base + control + entries + (align - 1)) .&. (0 - align)
      setField base mark arenaMark
      setField base regionStart start
      setField base regionEnd (start + region)
      setField base taken start
      setField base pagemap (base + control)
      setField base pagemapCommitted (base + control)
      Heap.pure base
  where
    ||| The bytes of the control block.
    controlBytes : Config -> Bits64
    controlBytes c = 8 * (emptyCount c 0 + classCount c)

||| Whether the address is an arena's, by its mark.
export
isArena : Pages h => (arena : Bits64) -> Heap.Op h Bool
isArena a = do
  m <- field a mark
  Heap.pure (m == arenaMark)

||| A largest chunk taken from the region, with the pagemap's entries for
||| it committed: its granule; nothing when the region or the memory is out.
export
carve : Pages h => Config -> (arena : Bits64) -> Heap.Op h (Maybe Bits64)
carve c a = do
  t <- field a taken
  e <- field a regionEnd
  let size = 1 `shiftL` c.maxChunkShift
  if t + size > e then Heap.pure Nothing else do
    g <- granuleOf c a t
    p <- field a pagemap
    pc <- field a pagemapCommitted
    let needed = p + ((g + (1 `shiftL` maxOrder c)) `shiftL` entryShift)
    want <- if needed <= pc then Heap.pure 0 else pages (needed - pc)
    ok <- if want == 0 then Heap.pure True else commit pc want
    if not ok then Heap.pure Nothing else do
      setField a pagemapCommitted (pc + want)
      setField a taken (t + size)
      Heap.pure (Just g)
