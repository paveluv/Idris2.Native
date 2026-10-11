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

import public Runtime.Collect
import public Runtime.Object
import public Runtime.State

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| End the program with the message, whatever operation was expected.
crashOp : String -> Op Heap a
crashOp msg = assert_total (idris_crash msg)

||| Memory committed to a space up to `need` and a window beyond, in whole
||| pages: `committed` and `end` are the state words of the space.
commitSpace : (committed, end : State) -> (need : Bits64) -> Op Heap ()
commitSpace committed end need = do
  have <- getState committed
  limit <- getState end
  win <- getState windowBytes
  if need <= have then pure () else do
    let upto = roundToPage (need + win)
    if upto > limit then crashOp "idris: the heap's reserved space is exhausted" else do
      commitMemory have (upto - have)
      setState committed upto

||| The first word of an object with a header, or of a continuation.
firstWord : Bits64 -> Op Heap Bits64
firstWord a = loadAt a 0

||| The size and the scanned words of the object at the address, by its
||| first word: a header's kind and parts, or a continuation's layout word,
||| which precedes the code its first word names.
sizeAt : Bits64 -> Op Heap Bits64
sizeAt a = do
  h <- firstWord a
  if isContinuation h
     then do l <- loadAt h (0 - 8); pure (continuationWords l)
     else pure (objectWords (kindOfHeader h) h)

scannedAt : Bits64 -> Op Heap (Bits64, Bits64)
scannedAt a = do
  h <- firstWord a
  if isContinuation h
     then do l <- loadAt h (0 - 8); pure (continuationScanned l)
     else pure (scannedWords (kindOfHeader h) h)

export
Memory Heap where
  collectable v = do
    tag <- pointerTag
    base <- getState fromBase
    hp <- allocationPointer
    let a = v - tag
    pure (prim__and_Bits64 v 1 == tag && base <= a && a < hp)
  addressOf v = do
    tag <- pointerTag
    pure (v - tag)
  pointerOf a = do
    tag <- pointerTag
    pure (a + tag)
  objectSize = sizeAt
  objectScanned = scannedAt
  forwarded a = do
    h <- firstWord a
    pure (if kindOfHeader h == forwardingId then Just (forwardedTo h) else Nothing)
  setForwarded from to = storeAt from 0 (forwardingHeader to)
  readWord a i = loadAt a (8 * i)
  writeWord a i v = storeAt a (8 * i) v
  reserve n = do
    top <- getState toTop
    let need = top + 8 * n
    commitSpace toCommitted toEnd need
    setState toTop need
    pure top
  nextToScan = do
    scan <- getState scanCursor
    top <- getState toTop
    if scan >= top then pure Nothing else do
      n <- sizeAt scan
      setState scanCursor (scan + 8 * n)
      pure (Just scan)
  rootCount = do
    nr <- nrootsArea
    loadAt nr 0
  readRoot i = do
    r <- rootsArea
    loadAt r (8 * i)
  writeRoot i v = do
    r <- rootsArea
    storeAt r (8 * i) v
  rootContinuation = continuation
  setRootContinuation = setContinuation
  flipSpaces = do
    fb <- getState fromBase
    fe <- getState fromEnd
    fc <- getState fromCommitted
    tb <- getState toBase
    te <- getState toEnd
    tc <- getState toCommitted
    tt <- getState toTop
    -- the old from-space is given back whole, and becomes the empty to-space
    releaseMemory fb (fc - fb)
    setState fromBase tb
    setState fromEnd te
    setState fromCommitted tc
    setState toBase fb
    setState toEnd fe
    setState toCommitted fb
    setState toTop fb
    setState scanCursor fb
    setState liveBytes (tt - tb)
    count <- getState collections
    setState collections (count + 1)
    -- the program allocates after the copies
    setAllocation tt tc

||| Room for `bytes` at the allocation pointer: the from-space committed to
||| a window beyond them, under the limit; the window moved past them; the
||| object's address.
grow : (bytes : Bits64) -> Op Heap Bits64
grow bytes = do
  hp <- allocationPointer
  base <- getState fromBase
  limit <- getState heapLimit
  win <- getState windowBytes
  let next = hp + bytes
  if limit /= 0 && next - base > prim__shr_Bits64 limit 1
     then crashOp "idris: heap limit exceeded"
     else do
       commitSpace fromCommitted fromEnd (next + win)
       setAllocation next (next + win)
       pure hp

%cg native flat Runtime.Space.allocSlow
||| `idris_alloc_slow`: the window is out; a collection first if the
||| from-space has grown past twice the live data, and a few windows at
||| least, then room for the object.
export covering
allocSlow : (bytes : Bits64) -> Op Heap (Addr k)
allocSlow bytes = do
  hp <- allocationPointer
  base <- getState fromBase
  live <- getState liveBytes
  win <- getState windowBytes
  let used = hp - base
  let threshold = if 2 * live > 4 * win then 2 * live else 4 * win
  if used + bytes > threshold then collect else pure ()
  a <- grow bytes
  pure (fromWord a)

%cg native flat Runtime.Space.allocMutable
||| `idris_alloc_mutable`: an object that will be written after it is made,
||| allocated by a call so that a collector with a nursery can keep it out
||| of it; in this one space, the window's bump or the slow path.
export covering
allocMutable : (bytes : Bits64) -> Op Heap (Addr k)
allocMutable bytes = do
  hp <- allocationPointer
  lim <- allocationLimit
  if hp + bytes <= lim
     then do
       setAllocation (hp + bytes) lim
       pure (fromWord hp)
     else allocSlow bytes

-- What a program may set and read of the heap, each a flat function that
-- ordinary code calls as any other.

%cg native flat Runtime.Space.setHeapLimit
||| The most bytes the heap may commit, 0 for no limit.
export
setHeapLimit : Bits64 -> IO ()
setHeapLimit bytes = primIO $ \w =>
  let (MkHeap # ()) = setState heapLimit bytes MkHeap in MkIORes () w

%cg native flat Runtime.Space.getHeapLimit
export
getHeapLimit : IO Bits64
getHeapLimit = primIO $ \w =>
  let (MkHeap # n) = getState heapLimit MkHeap in MkIORes n w

%cg native flat Runtime.Space.collectionCount
||| The collections so far.
export
collectionCount : IO Bits64
collectionCount = primIO $ \w =>
  let (MkHeap # n) = getState collections MkHeap in MkIORes n w
