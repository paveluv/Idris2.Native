||| The runtime's state: the words of the area `RUNTIME`, by name.
|||
||| The heap is two reserved ranges of address space, the spaces. One is the
||| from-space, where the program allocates: the allocation window lies in
||| it, and memory is committed to it a window at a time as the window
||| advances. The other is the to-space, empty between collections; a
||| collection copies what is live into it, and the two swap. What the last
||| collection left live decides when the next one runs, and the limit the
||| program sets decides how far the heap may grow.
module Runtime.State

import Runtime.Heap
import Runtime.Memory

import Compiler.Native.HeapObject.Kind

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| A word of the state, by its index in the area.
public export
State : Type
State = Bits64

||| The from-space: its first address, the end of its reservation, and the
||| end of the memory committed to it.
public export
fromBase, fromEnd, fromCommitted : State
fromBase = 0
fromEnd = 1
fromCommitted = 2

||| The to-space: the same, and during a collection the end of what has
||| been copied into it and the address of the next copy to scan.
public export
toBase, toEnd, toCommitted, toTop, scanCursor : State
toBase = 3
toEnd = 4
toCommitted = 5
toTop = 6
scanCursor = 7

||| The bytes the last collection left live; the most bytes the heap may
||| commit, 0 for no limit; the window's size; the collections so far.
public export
liveBytes, heapLimit, windowBytes, collections : State
liveBytes = 8
heapLimit = 9
windowBytes = 10
collections = 11

||| Sixteen bytes for a system call to write into: getrlimit's answer.
public export
scratchBytes : Bits64
scratchBytes = 8 * 16

||| The word of the state.
export
getState : State -> Op Heap Bits64
getState i = do
  rt <- runtimeArea
  loadAt rt (8 * i)

export
setState : State -> Bits64 -> Op Heap ()
setState i v = do
  rt <- runtimeArea
  storeAt rt (8 * i) v

||| The address of the scratch bytes.
export
scratchArea : Op Heap (Addr k)
scratchArea = do
  rt <- runtimeArea
  pure (fromWord (rt + scratchBytes))
