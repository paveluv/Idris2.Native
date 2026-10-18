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
|||
||| The semispace pair is the one space so far. Another (a nursery, a space
||| for large objects, a region of continuations) is a change to the core,
||| as a new shape is: the support tier, and code outside the runtime,
||| allocate in the spaces the core has, and never make one.
module Native.Runtime.Space

-- lint: allow public-import: the flat translation reaches through this module
-- (checking an importer's flat functions, it reaches this module's bodies,
-- which use it, so it is loaded wherever this module is)
import public Native.Runtime.State

import Native.Runtime.Bits
import Native.Runtime.Collect
import Native.Runtime.Memory
import Native.Runtime.Ordo
import Native.Runtime.PortTy
import Native.Runtime.Raw

import Native.Area
import Native.HeapObj.LayoutWord
import Native.HeapObj.Shape as HeapObj
import Native.Port
import Native.Routine
%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| Memory committed to a space up to `need` and a window beyond, in whole
||| pages: `committed` and `end` are the state words of the space.
commitSpace : (committed, end : State Raw) -> (need : Raw) -> Ordo.Op Ordo ()
commitSpace committed end need = do
  have <- State.getState committed
  limit <- State.getState end
  win <- State.getState State.windowBytes
  if need <= have then Ordo.pure () else do
    upto <- Memory.alignToPage (Raw.offset need win)
    if upto > limit then Ordo.crashOp "idris: the heap's reserved space is exhausted" else do
      Memory.commitMemory have (Raw.distance upto have)
      State.setState committed upto

||| The first word of an object with a header, or of a continuation, at an
||| address the collector holds as a word.
firstWord : Bits64 -> Ordo.Op Ordo Bits64
firstWord a = Memory.loadAt (Raw.fromWord a) 0

||| The collector's interface (`Memory`) holds addresses as words, as it
||| holds values: this module, its instance for the program's heap, makes
||| them the raw addresses the rest of the runtime's memory is reached by.
|||
||| The size and the scanned words of the object at the address, by its
||| first word: a header's shape and counts, or a continuation's layout
||| word, which precedes the code its first word names.
sizeAt : Bits64 -> Ordo.Op Ordo Bits64
sizeAt a = do
  h <- firstWord a
  if HeapObj.Shape.isFrame h
     then do l <- Memory.loadAt (Raw.fromWord h) (0 - 8); Ordo.pure (HeapObj.LayoutWord.continuationWords l)
     else Ordo.pure (HeapObj.Shape.objectWordsOf h)

export
Memory Ordo where
  collectable v = do
    tag <- Memory.pointerTag
    base <- State.getState State.fromBase
    hp <- Memory.allocationPointer
    let a = v - tag
    Ordo.pure (v .&. 1 == tag && Raw.rawWord base <= a && a < Raw.rawWord hp)
  addressOf v = do
    tag <- Memory.pointerTag
    Ordo.pure (v - tag)
  pointerOf a = do
    tag <- Memory.pointerTag
    Ordo.pure (a + tag)
  objectSize = sizeAt
  objectScanned = scannedAt
    where
      scannedAt : Bits64 -> Ordo.Op Ordo (Bits64, Bits64)
      scannedAt a = do
        h <- firstWord a
        if HeapObj.Shape.isFrame h
           then do l <- Memory.loadAt (Raw.fromWord h) (0 - 8); Ordo.pure (HeapObj.LayoutWord.continuationScanned l)
           else Ordo.pure (HeapObj.Shape.scannedOf h)
  forwarded a = do
    h <- firstWord a
    Ordo.pure (if HeapObj.Shape.isForwarding h then Just (HeapObj.Shape.forwardedTo h) else Nothing)
  setForwarded from to = Memory.storeAt (Raw.fromWord from) 0 (HeapObj.Shape.forwardingHeader to)
  readWord a i = Memory.loadAt (Raw.fromWord a) (8 * i)
  writeWord a i v = Memory.storeAt (Raw.fromWord a) (8 * i) v
  reserve n = do
    top <- State.getState State.toTop
    let need = Raw.offset top (8 * n)
    commitSpace State.toCommitted State.toEnd need
    State.setState State.toTop need
    Ordo.pure (Raw.rawWord top)
  nextToScan = do
    scan <- State.getState State.scanCursor
    top <- State.getState State.toTop
    if scan >= top then Ordo.pure Nothing else do
      n <- sizeAt (Raw.rawWord scan)
      State.setState State.scanCursor (Raw.offset scan (8 * n))
      Ordo.pure (Just (Raw.rawWord scan))
  rootCount = do
    nr <- Memory.nrootsArea
    Memory.loadAt nr 0
  readRoot i = do
    r <- Memory.rootsArea
    Memory.loadAt r (Area.rootOffset i)
  writeRoot i v = do
    r <- Memory.rootsArea
    Memory.storeAt r (Area.rootOffset i) v
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
    Memory.releaseMemory fb (Raw.distance fc fb)
    State.setState State.fromBase tb
    State.setState State.fromEnd te
    State.setState State.fromCommitted tc
    State.setState State.toBase fb
    State.setState State.toEnd fe
    State.setState State.toCommitted fb
    State.setState State.toTop fb
    State.setState State.scanCursor fb
    State.setState State.liveBytes (Raw.distance tt tb)
    count <- State.getState State.collections
    State.setState State.collections (count + 1)
    -- the program allocates after the copies
    Memory.setAllocation tt tc

||| Whether a collection is due before `bytes` more: the from-space has grown
||| past twice what the last collection left live, and four windows at least.
collectionDue : (bytes : Bits64) -> Ordo.Op Ordo Bool
collectionDue bytes = do
  hp <- Memory.allocationPointer
  base <- State.getState State.fromBase
  live <- State.getState State.liveBytes
  win <- State.getState State.windowBytes
  let threshold = if 2 * live > 4 * win then 2 * live else 4 * win
  Ordo.pure (Raw.distance hp base + bytes > threshold)

||| Room for `bytes` at the allocation pointer: the from-space committed to
||| a window beyond them, under the limit; the window moved past them; the
||| object's address.
grow : (bytes : Bits64) -> Ordo.Op Ordo Raw
grow bytes = do
  hp <- Memory.allocationPointer
  base <- State.getState State.fromBase
  limit <- State.getState State.heapLimit
  win <- State.getState State.windowBytes
  let next = Raw.offset hp bytes
  if limit /= 0 && Raw.distance next base > Bits.shiftR limit 1
     then Ordo.crashOp "idris: heap limit exceeded"
     else do
       commitSpace State.fromCommitted State.fromEnd (Raw.offset next win)
       Memory.setAllocation next (Raw.offset next win)
       Ordo.pure hp

%cg native flat Runtime.Space.allocSlow
||| `idris_alloc_slow`: the window is out; a collection first if the
||| from-space has grown past twice the live data, and a few windows at
||| least, then room for the object.
export covering
allocSlow : PortTy Memory.Addr (Routine.port Routine.AllocSlow)
allocSlow bytes = do
  due <- collectionDue bytes
  if due then Collect.collect else Ordo.pure ()
  a <- grow bytes
  Ordo.pure (Memory.objectAt a)

||| Room for `bytes` for the runtime's own objects, which the primitives
||| make: never a collection, since the primitives' callers hold values a
||| collection would move under them. When the window is out, the space
||| grows instead; if a collection was due, the window is left empty, so
||| that generated code's next allocation takes the slow path, which
||| collects. The space allocated past the window that way is bounded by one
||| primitive's objects. The object's address.
export
allocate : (bytes : Bits64) -> Ordo.Op Ordo Raw
allocate bytes = do
  hp <- Memory.allocationPointer
  lim <- Memory.allocationLimit
  if Raw.offset hp bytes <= lim
     then do
       Memory.setAllocation (Raw.offset hp bytes) lim
       Ordo.pure hp
     else do
       due <- collectionDue bytes
       a <- grow bytes
       hp' <- Memory.allocationPointer
       if due then Memory.setAllocation hp' hp' else Ordo.pure ()
       Ordo.pure a

%cg native flat Runtime.Space.allocMutable
||| `idris_alloc_mutable`: an object that will be written after it is made,
||| allocated by a call so that a collector with a nursery can keep it out
||| of it; in this one space, the window's bump or the slow path.
export covering
allocMutable : PortTy Memory.Addr (Routine.port Routine.AllocMutable)
allocMutable bytes = do
  hp <- Memory.allocationPointer
  lim <- Memory.allocationLimit
  if Raw.offset hp bytes <= lim
     then do
       Memory.setAllocation (Raw.offset hp bytes) lim
       Ordo.pure (Memory.objectAt hp)
     else allocSlow bytes

-- What a program may set and read of the heap, each a flat function that
-- ordinary code calls as any other.

%cg native flat Runtime.Space.setHeapLimit
||| The most bytes the heap may commit, 0 for no limit.
export
setHeapLimit : Bits64 -> IO ()
setHeapLimit bytes = primIO $ \w =>
  let (MkOrdo # ()) = State.setState State.heapLimit bytes MkOrdo in MkIORes () w

%cg native flat Runtime.Space.getHeapLimit
export
getHeapLimit : IO Bits64
getHeapLimit = primIO $ \w =>
  let (MkOrdo # n) = State.getState State.heapLimit MkOrdo in MkIORes n w

%cg native flat Runtime.Space.collectionCount
||| The collections so far.
export
collectionCount : IO Bits64
collectionCount = primIO $ \w =>
  let (MkOrdo # n) = State.getState State.collections MkOrdo in MkIORes n w
