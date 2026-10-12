||| Cheney's copying collector, written once against an interface to the
||| memory, so that it runs against the program's heap and against a model.
|||
||| Everything live is reached from the roots: the current continuation and
||| the root buffer. The collector forwards each root: a word that is not a
||| pointer into the space being collected is left as it is; one that points
||| to an object already moved becomes the pointer to its copy, which the
||| forwarding header the move left gives; any other object is copied to the
||| to-space, word by word, and its first word replaced by the forwarding
||| header. Then it scans the copies in the order they were made, forwarding
||| each word that holds a value, which may copy more objects after the scan
||| point; the scan ends when it reaches the end of the copies. Nothing is
||| recursive in the object graph's depth: the to-space is the queue.
|||
||| Every loop is a self tail call. The measures that end them: a copy
||| advances through the object's words; a scan through the object's
||| scanned words; the roots through the buffer; and the scan loop by the
||| words of the from-space not yet copied plus the words of the to-space
||| not yet scanned, which every step lowers.
module Runtime.Collect

import Runtime.Heap

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| What the collector needs of a memory. Addresses and values are words.
public export
interface Memory (0 h : Type) where
  ||| Whether a word is a pointer to an object in the space being collected.
  collectable : Bits64 -> Op h Bool
  ||| The address a pointer word points to, and the pointer word of an address.
  addressOf : Bits64 -> Op h Bits64
  pointerOf : Bits64 -> Op h Bits64
  ||| The words of the object at the address, and which of them hold values:
  ||| the first and how many.
  objectSize : Bits64 -> Op h Bits64
  objectScanned : Bits64 -> Op h (Bits64, Bits64)
  ||| Where the object at the address was moved to, if it was.
  forwarded : Bits64 -> Op h (Maybe Bits64)
  ||| Mark the object at the address as moved to the other.
  setForwarded : (from, to : Bits64) -> Op h ()
  ||| The word at the address's word index, and storing one.
  readWord : (addr, index : Bits64) -> Op h Bits64
  writeWord : (addr, index, value : Bits64) -> Op h ()
  ||| Room for the words in the to-space, after what is there: its address.
  reserve : (words : Bits64) -> Op h Bits64
  ||| The next copy in the to-space not yet scanned, advancing past it.
  nextToScan : Op h (Maybe Bits64)
  ||| The root buffer: the entries in use, one of them, and storing one.
  rootCount : Op h Bits64
  readRoot : Bits64 -> Op h Bits64
  writeRoot : (index, value : Bits64) -> Op h ()
  ||| The current continuation, a root of its own, and setting it.
  rootContinuation : Op h Bits64
  setRootContinuation : Bits64 -> Op h ()
  ||| The end of a collection: the to-space becomes the space the program
  ||| allocates in, and the old one is given back.
  flipSpaces : Op h ()

||| Copy the words of an object from one address to the other, from word
||| `i` to the count.
export covering
copyWords : Memory h => (from, to, i, count : Bits64) -> Op h ()
copyWords from to i count =
  if i >= count then pure () else do
    w <- readWord from i
    writeWord to i w
    copyWords from to (i + 1) count

||| A word forwarded: itself unless it points into the space being
||| collected; the pointer to the copy of what it points to, made now if
||| the object was not moved yet.
export covering
forward : Memory h => Bits64 -> Op h Bits64
forward v = do
  c <- collectable v
  if not c then pure v else do
    a <- addressOf v
    moved <- forwarded a
    case moved of
      Just to => pointerOf to
      Nothing => do
        n <- objectSize a
        to <- reserve n
        copyWords a to 0 n
        setForwarded a to
        pointerOf to

||| Forward the words of the copy at the address that hold values, from
||| word `i` to the end.
export covering
forwardWords : Memory h => (addr, i, end : Bits64) -> Op h ()
forwardWords addr i end =
  if i >= end then pure () else do
    v <- readWord addr i
    v' <- forward v
    writeWord addr i v'
    forwardWords addr (i + 1) end

||| Scan one copy.
export covering
scanObject : Memory h => Bits64 -> Op h ()
scanObject addr = do
  (from, count) <- objectScanned addr
  forwardWords addr from (from + count)

||| Scan the copies until none is left to scan.
export covering
scanLoop : Memory h => Op h ()
scanLoop = do
  next <- nextToScan
  case next of
    Nothing => pure ()
    Just addr => do
      scanObject addr
      scanLoop

||| Forward the root buffer's entries from `i` to the count.
export covering
forwardRoots : Memory h => (i, count : Bits64) -> Op h ()
forwardRoots i count =
  if i >= count then pure () else do
    v <- readRoot i
    v' <- forward v
    writeRoot i v'
    forwardRoots (i + 1) count

||| A collection: the roots forwarded, the copies scanned, the spaces
||| flipped.
export covering
collect : Memory h => Op h ()
collect = do
  k <- rootContinuation
  k' <- forward k
  setRootContinuation k'
  n <- rootCount
  forwardRoots 0 n
  scanLoop
  flipSpaces
