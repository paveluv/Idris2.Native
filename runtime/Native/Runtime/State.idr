||| The runtime's state: the words of the area `RUNTIME`, by name.
|||
||| The heap is two reserved ranges of address space, the spaces. One is the
||| from-space, where the program allocates: the allocation window lies in
||| it, and memory is committed to it a window at a time as the window
||| advances. The other is the to-space, empty between collections; a
||| collection copies what is live into it, and the two swap. What the last
||| collection left live decides when the next one runs, and the limit the
||| program sets decides how far the heap may grow.
|||
||| The state's words are named fields (`Native.Field`), as a mutable
||| record's raw words are, each of the carrier it holds, and read and
||| written by its name, as that carrier's type (`get`, `set`): an address
||| as a byte address, a count as a word, never one taken for the other.
||| Code that is handed a word of the state, not the name, takes it as a
||| reference made by the name (`word`), which nothing else makes. The
||| fields fit the area, its scratch bytes after them, as `fit` proves, so a
||| state that grew past its area is refused where the runtime is built.
module Native.Runtime.State

import Native.Runtime.ByteAddr
import Native.Runtime.Cell
import Native.Runtime.Memory
import Native.Runtime.Ordo
import Native.Runtime.PortTy

import Native.Area
import Native.Carrier
import Native.Field
import Native.Mach

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

-- lint: allow public-unneeded: the search on a name, where a word is read or
-- written, unfolds the list
||| The state's words, in the area's order:
|||
||| - the from-space's first address, the end of its reservation, and the
|||   end of the memory committed to it;
||| - the to-space's, and during a collection the end of what has been
|||   copied into it and the address of the next copy to scan;
||| - the bytes the last collection left live, the most bytes the heap may
|||   commit, 0 for no limit, the window's size and the collections so far;
||| - the arena of the process's allocator of memory outside the heap
|||   (`Alloc.System`), null until the first allocation makes it;
||| - the array of the environment's blocks (`Alloc.Blocks.environment`),
|||   null while the environment is the one the system gave, which only the
|||   allocator's sealed modules read or write;
||| - why the last OS service that failed did, by the reason's code
|||   (`Native.Failure`), 0 until one fails: each service that fails sets
|||   it, and none that succeeds clears it, as the C library's `errno`.
public export
Fields : List (String, Carrier)
Fields =
  [ "fromBase" ~: Carrier.ByteAddr, "fromEnd" ~: Carrier.ByteAddr
  , "fromCommitted" ~: Carrier.ByteAddr
  , "toBase" ~: Carrier.ByteAddr, "toEnd" ~: Carrier.ByteAddr, "toCommitted" ~: Carrier.ByteAddr
  , "toTop" ~: Carrier.ByteAddr, "scanCursor" ~: Carrier.ByteAddr
  , "liveBytes" ~: Mach.U64, "heapLimit" ~: Mach.U64, "windowBytes" ~: Mach.U64
  , "collections" ~: Mach.U64
  , "foreignArena" ~: Carrier.ByteAddr
  , "environArray" ~: Carrier.ByteAddr
  , "lastFailure" ~: Mach.U64 ]

||| The words of scratch bytes, sixteen bytes, that a system call writes
||| into, getrlimit's answer: the first, after the fields, and how many.
scratch, scratchWords : Bits64
scratch = 15
scratchWords = 2

||| The state's names are each one word's, all raw, the scratch bytes after
||| them, and all of it fits the area.
0 fit : (Field.distinct Fields, Field.counts Fields,
         State.scratch + State.scratchWords <= Area.runtimeWords) =
        (True, (State.scratch, 0), True)
fit = Refl

||| A word of the state, of the carrier it holds: made by its name alone
||| (`word`), for code that is handed the word rather than its name.
export
record State (0 c : Carrier) where
  constructor MkState
  index : Bits64

||| The word of the name.
export %inline
word : (0 n : String) -> {i : Bits64} -> {0 j : Bits64} ->
       {auto 0 at : Field.Named n Fields i j c} -> State c
word _ = MkState i

||| The word, as the type its carrier says, and storing one.
export
load : Cell (PortTy.Carried () c) => State c -> Ordo.Op Ordo (PortTy.Carried () c)
load s = do
  rt <- Memory.runtimeArea
  w <- Memory.loadAt rt (8 * s.index)
  Ordo.pure (Cell.fromCell w)

export
store : Cell (PortTy.Carried () c) => State c -> PortTy.Carried () c -> Ordo.Op Ordo ()
store s v = do
  rt <- Memory.runtimeArea
  Memory.storeAt rt (8 * s.index) (Cell.toCell v)

||| The word of the name, as the type its carrier says, and storing one.
export %inline
get : (0 n : String) -> {i : Bits64} -> {0 j : Bits64} -> {0 c : Carrier} ->
      {auto 0 at : Field.Named n Fields i j c} -> Cell (PortTy.Carried () c) =>
      Ordo.Op Ordo (PortTy.Carried () c)
get n = load (word n)

export %inline
set : (0 n : String) -> {i : Bits64} -> {0 j : Bits64} -> {0 c : Carrier} ->
      {auto 0 at : Field.Named n Fields i j c} -> Cell (PortTy.Carried () c) =>
      PortTy.Carried () c -> Ordo.Op Ordo ()
set n v = store (word n) v

||| The byte address of the scratch bytes, since they hold no object.
export
scratchArea : Ordo.Op Ordo ByteAddr
scratchArea = do
  rt <- Memory.runtimeArea
  Ordo.pure (ByteAddr.offset rt (8 * scratch))
