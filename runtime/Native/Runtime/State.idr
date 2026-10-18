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

import Native.Runtime.Memory
import Native.Runtime.Ordo
import Native.Runtime.Raw

import Native.Area

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| What a word of the state holds: an address, or a count.
public export
data Holds : Type -> Type where
  AnAddress : Holds Raw
  ACount : Holds Bits64

||| A word of the state, by its index in the area, and what it holds.
public export
record State (t : Type) where
  constructor MkState
  index : Bits64
  holds : Holds t

||| The state's word `i`, which the area holds, an address or a count: a
||| word past the area's (`Area.runtimeWords`) does not typecheck.
public export
address : (i : Bits64) -> {auto 0 fits : i < Area.runtimeWords = True} -> State Raw
address i = MkState i AnAddress

public export
count : (i : Bits64) -> {auto 0 fits : i < Area.runtimeWords = True} -> State Bits64
count i = MkState i ACount

||| The from-space: its first address, the end of its reservation, and the
||| end of the memory committed to it.
public export
fromBase, fromEnd, fromCommitted : State Raw
fromBase = address 0
fromEnd = address 1
fromCommitted = address 2

||| The to-space: the same, and during a collection the end of what has
||| been copied into it and the address of the next copy to scan.
public export
toBase, toEnd, toCommitted, toTop, scanCursor : State Raw
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
foreignArena : State Raw
foreignArena = address 12

||| The process's environment, once the program changed it
||| (`Support.Environment`): the array of its entries' addresses, null
||| while the environment is the one the system gave; its entries; and the
||| entries it has room for.
export
environArray : State Raw
environArray = address 13

export
environCount, environCapacity : State Bits64
environCount = count 14
environCapacity = count 15

||| The first of the `n` words of the state from its word `i`, all of which
||| the area holds: a run of raw words.
public export
words : (i, n : Bits64) -> {auto 0 fits : i + n <= Area.runtimeWords = True} -> Bits64
words i _ = i

||| The word of the state, as what it holds: the state keeps an address as
||| its word.
export
getState : State t -> Ordo.Op Ordo t
getState (MkState i AnAddress) = do
  rt <- Memory.runtimeArea
  w <- Memory.loadAt rt (8 * i)
  Ordo.pure (Raw.fromWord w)
getState (MkState i ACount) = do
  rt <- Memory.runtimeArea
  Memory.loadAt rt (8 * i)

export
setState : State t -> t -> Ordo.Op Ordo ()
setState (MkState i AnAddress) v = do
  rt <- Memory.runtimeArea
  Memory.storeAt rt (8 * i) (Raw.rawWord v)
setState (MkState i ACount) v = do
  rt <- Memory.runtimeArea
  Memory.storeAt rt (8 * i) v

||| The address of the scratch bytes, raw memory, since they hold no object.
export
scratchArea : Ordo.Op Ordo Raw
scratchArea = do
  rt <- Memory.runtimeArea
  Ordo.pure (Raw.offset rt (8 * scratch))
  where
    ||| The first of the two words, sixteen bytes, that a system call writes
    ||| into: getrlimit's answer.
    scratch : Bits64
    scratch = words 16 2
