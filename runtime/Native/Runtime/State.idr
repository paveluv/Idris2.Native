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

import Native.Runtime.Heap
import Native.Runtime.Memory

import Native.Area

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| A word of the state, by its index in the area.
public export
State : Type
State = Bits64

||| The state's word `i`, which the area holds: a word past the area's
||| (`Area.runtimeWords`) does not typecheck.
public export
word : (i : Bits64) -> {auto 0 fits : i < Area.runtimeWords = True} -> State
word i = i

||| The first of the `n` words of the state from its word `i`, all of which
||| the area holds.
public export
words : (i, n : Bits64) -> {auto 0 fits : i + n <= Area.runtimeWords = True} -> State
words i _ = i

||| The from-space: its first address, the end of its reservation, and the
||| end of the memory committed to it.
public export
fromBase, fromEnd, fromCommitted : State
fromBase = word 0
fromEnd = word 1
fromCommitted = word 2

||| The to-space: the same, and during a collection the end of what has
||| been copied into it and the address of the next copy to scan.
public export
toBase, toEnd, toCommitted, toTop, scanCursor : State
toBase = word 3
toEnd = word 4
toCommitted = word 5
toTop = word 6
scanCursor = word 7

||| The bytes the last collection left live; the most bytes the heap may
||| commit, 0 for no limit; the window's size; the collections so far.
export
liveBytes, heapLimit, windowBytes, collections : State
liveBytes = word 8
heapLimit = word 9
windowBytes = word 10
collections = word 11

||| Two words, sixteen bytes, for a system call to write into: getrlimit's
||| answer.
public export
scratch : State
scratch = words 16 2

||| The word of the state.
export
getState : State -> Heap.Op Heap Bits64
getState i = do
  rt <- Memory.runtimeArea
  Memory.loadAt rt (8 * i)

export
setState : State -> Bits64 -> Heap.Op Heap ()
setState i v = do
  rt <- Memory.runtimeArea
  Memory.storeAt rt (8 * i) v

||| The address of the scratch bytes, as a word, since they hold no object.
export
scratchArea : Heap.Op Heap Bits64
scratchArea = do
  rt <- Memory.runtimeArea
  Heap.pure (rt + 8 * scratch)
