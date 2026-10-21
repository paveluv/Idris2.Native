||| The runtime's state: the words of the area `RUNTIME`, by name.
|||
||| The heap is two reserved ranges of address space, the spaces. One is the
||| from-space, where the program allocates: the allocation window lies in
||| it, and memory is committed to it a window at a time as the window
||| advances. The other is the to-space, empty between collections; a
||| collection copies what is live into it, and the two swap. What the last
||| collection left live decides when the next one runs, and the limit the
||| program sets decides how far the heap may grow.
module Native.Runtime.State

import Native.Runtime.ByteAddr
import Native.Runtime.Memory
import Native.Runtime.Ordo

import Native.Area

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| What a word of the state can hold, and how it is that word: an address,
||| which the state keeps as its word, or a count. By the type, so that
||| each access is the one of its kind: a copy of `getState` for one kind
||| holds no alternative of the other's.
public export
interface Cell t where
  fromCell : Bits64 -> t
  toCell : t -> Bits64

public export
Cell ByteAddr where
  fromCell = ByteAddr.fromWord
  toCell = ByteAddr.toWord

public export
Cell Bits64 where
  fromCell w = w
  toCell w = w

||| A word of the state, by its index in the area; what it holds is its
||| type's (`Cell`).
public export
record State (t : Type) where
  constructor MkState
  index : Bits64

||| The state's word `i`, which the area holds, an address or a count: a
||| word past the area's (`Area.runtimeWords`) does not typecheck.
public export
address : (i : Bits64) -> {auto 0 fits : i < Area.runtimeWords = True} -> State ByteAddr
address i = MkState i

public export
count : (i : Bits64) -> {auto 0 fits : i < Area.runtimeWords = True} -> State Bits64
count i = MkState i

||| The from-space: its first address, the end of its reservation, and the
||| end of the memory committed to it.
public export
fromBase, fromEnd, fromCommitted : State ByteAddr
fromBase = address 0
fromEnd = address 1
fromCommitted = address 2

||| The to-space: the same, and during a collection the end of what has
||| been copied into it and the address of the next copy to scan.
public export
toBase, toEnd, toCommitted, toTop, scanCursor : State ByteAddr
toBase = address 3
toEnd = address 4
toCommitted = address 5
toTop = address 6
scanCursor = address 7

||| The bytes the last collection left live; the most bytes the heap may
||| commit, 0 for no limit; the window's size; the collections so far.
export
liveBytes, heapLimit, windowBytes, collections : State Bits64
liveBytes = count 8
heapLimit = count 9
windowBytes = count 10
collections = count 11

||| The arena of the process's allocator of memory outside the heap
||| (`Alloc.System`), null until the first allocation makes it.
export
foreignArena : State ByteAddr
foreignArena = address 12

||| The array of the environment's blocks (`Alloc.Blocks.environment`),
||| null while the environment is the one the system gave. Only the
||| allocator's sealed modules read or write it. Words 14 and 15 are free.
export
environArray : State ByteAddr
environArray = address 13

||| Why the last OS service that failed did, by the reason's code
||| (`Native.Failure`); 0 until one fails. Each service that fails sets it,
||| and none that succeeds clears it, as the C library's `errno`.
export
lastFailure : State Bits64
lastFailure = count 18

||| The first of the `n` words of the state from its word `i`, all of which
||| the area holds: a run of raw words.
public export
words : (i, n : Bits64) -> {auto 0 fits : i + n <= Area.runtimeWords = True} -> Bits64
words i _ = i

||| The word of the state, as what it holds: the state keeps an address as
||| its word.
export
getState : Cell t => State t -> Ordo.Op Ordo t
getState s = do
  rt <- Memory.runtimeArea
  w <- Memory.loadAt rt (8 * s.index)
  Ordo.pure (fromCell w)

export
setState : Cell t => State t -> t -> Ordo.Op Ordo ()
setState s v = do
  rt <- Memory.runtimeArea
  Memory.storeAt rt (8 * s.index) (toCell v)

||| The byte address of the scratch bytes, since they hold no object.
export
scratchArea : Ordo.Op Ordo ByteAddr
scratchArea = do
  rt <- Memory.runtimeArea
  Ordo.pure (ByteAddr.offset rt (8 * scratch))
  where
    ||| The first of the two words, sixteen bytes, that a system call writes
    ||| into: getrlimit's answer.
    scratch : Bits64
    scratch = words 16 2
