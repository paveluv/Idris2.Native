||| The heap's spaces, and the allocation slow paths that manage them: the
||| program's memory, as `Runtime.Collect`'s interface sees it.
|||
||| The from-space is where the program allocates, through the inline bump
||| of the allocation window. When the window runs out, `allocSlow` either
||| extends it, committing memory to the from-space, or, when the space has
||| grown past twice what the last collection left live (and a few windows
||| at least), collects first: the live objects are copied to the to-space,
||| the spaces swap, and the old one is given back to the system. A limit the
||| program sets bounds the heap: a copying collector holds two spaces, so
||| the data may reach half of it.
|||
||| Nothing here collects except `allocSlow`, which generated code calls
||| from the stub that has saved its live values in the root buffer. The
||| runtime's own allocation never collects.
module Runtime.Space

-- lint: allow public-import: the flat translation reaches through this module
-- (checking an importer's flat functions, it reaches this module's bodies,
-- which use it, so it is loaded wherever this module is)
import public Runtime.State

import Runtime.Bits
import Runtime.Collect
import Runtime.Heap
import Runtime.Memory
import Runtime.Object

import HeapObj.Kind as HeapObj
%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| Memory committed to a space up to `need` and a window beyond, in whole
||| pages: `committed` and `end` are the state words of the space.
commitSpace : (committed, end : State) -> (need : Bits64) -> Heap.Op Heap ()
commitSpace committed end need = do
  have <- State.getState committed
  limit <- State.getState end
  win <- State.getState State.windowBytes
  if need <= have then Heap.pure () else do
    upto <- Memory.roundToPage (need + win)
    if upto > limit then Heap.crashOp "idris: the heap's reserved space is exhausted" else do
      Memory.commitMemory have (upto - have)
      State.setState committed upto

||| The first word of an object with a header, or of a continuation.
firstWord : Bits64 -> Heap.Op Heap Bits64
firstWord a = Memory.loadAt a 0

||| The size and the scanned words of the object at the address, by its
||| first word: a header's kind and parts, or a continuation's layout word,
||| which precedes the code its first word names.
sizeAt : Bits64 -> Heap.Op Heap Bits64
sizeAt a = do
  h <- firstWord a
  if Object.isContinuation h
     then do l <- Memory.loadAt h (0 - 8); Heap.pure (Object.continuationWords l)
     else Heap.pure (Object.objectWords (Object.kindOfHeader h) h)

export
Memory Heap where
  collectable v = do
    tag <- Memory.pointerTag
    base <- State.getState State.fromBase
    hp <- Memory.allocationPointer
    let a = v - tag
    Heap.pure (v .&. 1 == tag && base <= a && a < hp)
  addressOf v = do
    tag <- Memory.pointerTag
    Heap.pure (v - tag)
  pointerOf a = do
    tag <- Memory.pointerTag
    Heap.pure (a + tag)
  objectSize = sizeAt
  objectScanned = scannedAt
    where
      scannedAt : Bits64 -> Heap.Op Heap (Bits64, Bits64)
      scannedAt a = do
        h <- firstWord a
        if Object.isContinuation h
           then do l <- Memory.loadAt h (0 - 8); Heap.pure (Object.continuationScanned l)
           else Heap.pure (Object.scannedWords (Object.kindOfHeader h) h)
  forwarded a = do
    h <- firstWord a
    Heap.pure (if Object.kindOfHeader h == Object.forwardingId then Just (Object.forwardedTo h) else Nothing)
  setForwarded from to = Memory.storeAt from 0 (Object.forwardingHeader to)
  readWord a i = Memory.loadAt a (8 * i)
  writeWord a i v = Memory.storeAt a (8 * i) v
  reserve n = do
    top <- State.getState State.toTop
    let need = top + 8 * n
    commitSpace State.toCommitted State.toEnd need
    State.setState State.toTop need
    Heap.pure top
  nextToScan = do
    scan <- State.getState State.scanCursor
    top <- State.getState State.toTop
    if scan >= top then Heap.pure Nothing else do
      n <- sizeAt scan
      State.setState State.scanCursor (scan + 8 * n)
      Heap.pure (Just scan)
  rootCount = do
    nr <- Memory.nrootsArea
    Memory.loadAt nr 0
  readRoot i = do
    r <- Memory.rootsArea
    Memory.loadAt r (8 * i)
  writeRoot i v = do
    r <- Memory.rootsArea
    Memory.storeAt r (8 * i) v
  rootContinuation = Memory.continuation
  setRootContinuation = Memory.setContinuation
  flipSpaces = do
    fb <- State.getState State.fromBase
    fe <- State.getState State.fromEnd
    fc <- State.getState State.fromCommitted
    tb <- State.getState State.toBase
    te <- State.getState State.toEnd
    tc <- State.getState State.toCommitted
    tt <- State.getState State.toTop
    -- the old from-space is given back whole, and becomes the empty to-space
    Memory.releaseMemory fb (fc - fb)
    State.setState State.fromBase tb
    State.setState State.fromEnd te
    State.setState State.fromCommitted tc
    State.setState State.toBase fb
    State.setState State.toEnd fe
    State.setState State.toCommitted fb
    State.setState State.toTop fb
    State.setState State.scanCursor fb
    State.setState State.liveBytes (tt - tb)
    count <- State.getState State.collections
    State.setState State.collections (count + 1)
    -- the program allocates after the copies
    Memory.setAllocation tt tc

||| Whether a collection is due before `bytes` more: the from-space has grown
||| past twice what the last collection left live, and four windows at least.
collectionDue : (bytes : Bits64) -> Heap.Op Heap Bool
collectionDue bytes = do
  hp <- Memory.allocationPointer
  base <- State.getState State.fromBase
  live <- State.getState State.liveBytes
  win <- State.getState State.windowBytes
  let threshold = if 2 * live > 4 * win then 2 * live else 4 * win
  Heap.pure (hp - base + bytes > threshold)

||| Room for `bytes` at the allocation pointer: the from-space committed to
||| a window beyond them, under the limit; the window moved past them; the
||| object's address.
grow : (bytes : Bits64) -> Heap.Op Heap Bits64
grow bytes = do
  hp <- Memory.allocationPointer
  base <- State.getState State.fromBase
  limit <- State.getState State.heapLimit
  win <- State.getState State.windowBytes
  let next = hp + bytes
  if limit /= 0 && next - base > Bits.shiftR limit 1
     then Heap.crashOp "idris: heap limit exceeded"
     else do
       commitSpace State.fromCommitted State.fromEnd (next + win)
       Memory.setAllocation next (next + win)
       Heap.pure hp

%cg native flat Runtime.Space.allocSlow
||| `idris_alloc_slow`: the window is out; a collection first if the
||| from-space has grown past twice the live data, and a few windows at
||| least, then room for the object.
export covering
allocSlow : (bytes : Bits64) -> Heap.Op Heap (Memory.Addr k)
allocSlow bytes = do
  due <- collectionDue bytes
  if due then Collect.collect else Heap.pure ()
  a <- grow bytes
  Heap.pure (Memory.fromWord a)

||| Room for `bytes` for the runtime's own objects, which the primitives
||| make: never a collection, since the primitives' callers hold values a
||| collection would move under them. When the window is out, the space
||| grows instead; if a collection was due, the window is left empty, so
||| that generated code's next allocation takes the slow path, which
||| collects. The space allocated past the window that way is bounded by one
||| primitive's objects. The object's address.
export
allocate : (bytes : Bits64) -> Heap.Op Heap Bits64
allocate bytes = do
  hp <- Memory.allocationPointer
  lim <- Memory.allocationLimit
  if hp + bytes <= lim
     then do
       Memory.setAllocation (hp + bytes) lim
       Heap.pure hp
     else do
       due <- collectionDue bytes
       a <- grow bytes
       hp' <- Memory.allocationPointer
       if due then Memory.setAllocation hp' hp' else Heap.pure ()
       Heap.pure a

%cg native flat Runtime.Space.allocMutable
||| `idris_alloc_mutable`: an object that will be written after it is made,
||| allocated by a call so that a collector with a nursery can keep it out
||| of it; in this one space, the window's bump or the slow path.
export covering
allocMutable : (bytes : Bits64) -> Heap.Op Heap (Memory.Addr k)
allocMutable bytes = do
  hp <- Memory.allocationPointer
  lim <- Memory.allocationLimit
  if hp + bytes <= lim
     then do
       Memory.setAllocation (hp + bytes) lim
       Heap.pure (Memory.fromWord hp)
     else allocSlow bytes

-- What a program may set and read of the heap, each a flat function that
-- ordinary code calls as any other.

%cg native flat Runtime.Space.setHeapLimit
||| The most bytes the heap may commit, 0 for no limit.
export
setHeapLimit : Bits64 -> IO ()
setHeapLimit bytes = primIO $ \w =>
  let (Heap.MkHeap # ()) = State.setState State.heapLimit bytes Heap.MkHeap in MkIORes () w

%cg native flat Runtime.Space.getHeapLimit
export
getHeapLimit : IO Bits64
getHeapLimit = primIO $ \w =>
  let (Heap.MkHeap # n) = State.getState State.heapLimit Heap.MkHeap in MkIORes n w

%cg native flat Runtime.Space.collectionCount
||| The collections so far.
export
collectionCount : IO Bits64
collectionCount = primIO $ \w =>
  let (Heap.MkHeap # n) = State.getState State.collections Heap.MkHeap in MkIORes n w
