||| Memory: addresses, and the reads and writes at them.
|||
||| An address is a word. This module is the only one that makes one from a
||| word or takes one apart: elsewhere an address comes only from an
||| operation that returns one, so no other word is used as an address by
||| mistake. Every access is at an address plus a byte offset, and threads
||| the token, so that accesses happen in the order the code gives them.
|||
||| The accesses are the inline externs (`Native.Intrinsic` says what they
||| are), each declared here, privately, by its port, and wrapped for the
||| rest of the runtime; the code generator finds each by that type.
module Native.Runtime.Memory

-- lint: allow public-import: the flat translation reaches through this module
-- (checking an importer's flat functions, it reaches this module's bodies,
-- which use it, so it is loaded wherever this module is)
import public Native.Intrinsic
import public Native.Port
import public Native.Runtime.OS
-- lint: allow public-import: an extern's type, written by its port, reduces only
-- where the port and its reading are visible, so they are wherever this
-- module is, whose wrappers the flat translation unfolds into its importers
import public Native.Runtime.PortTy

-- the runtime's own, never re-exported: each module that uses it imports it
import Native.Runtime.Bits
import Native.Runtime.Heap

import Native.Flat.Uniform as Flat
import Native.HeapObj.Shape as HeapObj

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

%extern intrinsic__load64 : PortTy.ExternTy (Intrinsic.port Intrinsic.Load64)
%extern intrinsic__load32 : PortTy.ExternTy (Intrinsic.port Intrinsic.Load32)
%extern intrinsic__load16 : PortTy.ExternTy (Intrinsic.port Intrinsic.Load16)
%extern intrinsic__load8 : PortTy.ExternTy (Intrinsic.port Intrinsic.Load8)
%extern intrinsic__store64 : PortTy.ExternTy (Intrinsic.port Intrinsic.Store64)
%extern intrinsic__store32 : PortTy.ExternTy (Intrinsic.port Intrinsic.Store32)
%extern intrinsic__store16 : PortTy.ExternTy (Intrinsic.port Intrinsic.Store16)
%extern intrinsic__store8 : PortTy.ExternTy (Intrinsic.port Intrinsic.Store8)
%extern intrinsic__getHp : PortTy.ExternTy (Intrinsic.port Intrinsic.GetHp)
%extern intrinsic__setHp : PortTy.ExternTy (Intrinsic.port Intrinsic.SetHp)
%extern intrinsic__getHpLim : PortTy.ExternTy (Intrinsic.port Intrinsic.GetHpLim)
%extern intrinsic__setHpLim : PortTy.ExternTy (Intrinsic.port Intrinsic.SetHpLim)
%extern intrinsic__getK : PortTy.ExternTy (Intrinsic.port Intrinsic.GetK)
%extern intrinsic__setK : PortTy.ExternTy (Intrinsic.port Intrinsic.SetK)
%extern intrinsic__pointerTag : PortTy.ExternTy (Intrinsic.port Intrinsic.PointerTag)
%extern intrinsic__stackLimitArea : PortTy.ExternTy (Intrinsic.port Intrinsic.StackLimitArea)
%extern intrinsic__argvArea : PortTy.ExternTy (Intrinsic.port Intrinsic.ArgvArea)
%extern intrinsic__rootsArea : PortTy.ExternTy (Intrinsic.port Intrinsic.RootsArea)
%extern intrinsic__nrootsArea : PortTy.ExternTy (Intrinsic.port Intrinsic.NrootsArea)
%extern intrinsic__runtimeArea : PortTy.ExternTy (Intrinsic.port Intrinsic.RuntimeArea)
%extern intrinsic__valueWord : PortTy.ExternTy (Intrinsic.port Intrinsic.ValueWord)
%extern intrinsic__wordValue : PortTy.ExternTy (Intrinsic.port Intrinsic.WordValue)

||| The address of an object of the shape `s`, or of memory the runtime
||| maps. The core knows objects by their shapes only; the types an object
||| may be are the support tier's (`Native.Support.Obj`).
export
record Addr (0 s : HeapObj.Shape) where
  constructor MkAddr
  word : Bits64


||| The word at the address plus the offset.
export %inline
load64 : Addr s -> (offset : Bits64) -> Heap.Op Heap Bits64
load64 a = intrinsic__load64 a.word

||| The 32, 16 or 8 bits at the address plus the offset, as a word.
export %inline
load32, load16, load8 : Addr s -> (offset : Bits64) -> Heap.Op Heap Bits64
load32 a = intrinsic__load32 a.word
load16 a = intrinsic__load16 a.word
load8 a = intrinsic__load8 a.word

||| Store the word at the address plus the offset.
export %inline
store64 : Addr s -> (offset, value : Bits64) -> Heap.Op Heap ()
store64 a = intrinsic__store64 a.word

||| Store the word's low 32, 16 or 8 bits at the address plus the offset.
export %inline
store32, store16, store8 : Addr s -> (offset, value : Bits64) -> Heap.Op Heap ()
store32 a = intrinsic__store32 a.word
store16 a = intrinsic__store16 a.word
store8 a = intrinsic__store8 a.word

------------------------------------------------------------------------------
-- Words as addresses, for the module that manages the spaces

||| The address a word is: for the modules that lay out the heap's spaces
||| and its objects, which compute addresses as words.
export %inline
fromWord : Bits64 -> Addr s
fromWord = MkAddr

||| The word an address is.
export %inline
toWord : Addr s -> Bits64
toWord a = a.word

||| The word at an address plus a byte offset, both words, and storing one:
||| the loads and stores for code that works on addresses as words.
export %inline
loadAt : (base, offset : Bits64) -> Heap.Op Heap Bits64
loadAt = intrinsic__load64

export %inline
storeAt : (base, offset, value : Bits64) -> Heap.Op Heap ()
storeAt = intrinsic__store64

------------------------------------------------------------------------------
-- The pinned registers, the encoding, the areas


||| The allocation window: inline allocation bumps the allocation pointer
||| until the limit, and takes the slow path past it.
export %inline
allocationPointer : Heap.Op Heap Bits64
allocationPointer = intrinsic__getHp

export %inline
allocationLimit : Heap.Op Heap Bits64
allocationLimit = intrinsic__getHpLim

export %inline
setAllocation : (hp, hplim : Bits64) -> Heap.Op Heap ()
setAllocation hp hplim = do
  intrinsic__setHp hp
  intrinsic__setHpLim hplim

||| Make `bytes` at the address the allocation window.
export
setWindow : Addr s -> (bytes : Bits64) -> Heap.Op Heap ()
setWindow a bytes = setAllocation a.word (a.word + bytes)

||| The current continuation, as the pointer word it is, and setting it:
||| the collector's first root, which it rewrites when it moves the
||| continuation. The conversions between the continuation and its word are
||| this module's, so these are not inlined into their callers.
export
continuation : Heap.Op Heap Bits64
continuation = intrinsic__getK

export
setContinuation : Bits64 -> Heap.Op Heap ()
setContinuation = intrinsic__setK

||| The pointer tag of the program's encoding: a pointer word is the
||| object's address plus the tag, and a word is a pointer exactly when its
||| low bit is the tag's. The runtime's one knowledge of the encoding.
export %inline
pointerTag : Heap.Op Heap Bits64
pointerTag = intrinsic__pointerTag

||| The per-thread areas, as the words of their addresses, since they hold
||| no object: the word that holds the lowest the machine stack pointer may
||| go in direct code; the word that holds the stack pointer at the
||| program's entry, where the argument count, the arguments' addresses and
||| the environment's are; the root buffer and the word that counts its
||| entries in use; and the runtime's state.
export %inline
stackLimitArea : Heap.Op Heap Bits64
stackLimitArea = intrinsic__stackLimitArea

export %inline
argvArea : Heap.Op Heap Bits64
argvArea = intrinsic__argvArea

export %inline
rootsArea : Heap.Op Heap Bits64
rootsArea = intrinsic__rootsArea

export %inline
nrootsArea : Heap.Op Heap Bits64
nrootsArea = intrinsic__nrootsArea

export %inline
runtimeArea : Heap.Op Heap Bits64
runtimeArea = intrinsic__runtimeArea

------------------------------------------------------------------------------
-- Values as ordinary code holds them, and the objects they point to


||| The object a value is, and the value an object is, for a type whose
||| values ordinary code holds as objects of the shape `s` always, such as a
||| string, or a list, whose `[]` is a static object: the caller, which
||| knows the type, says the shape. These never test the word. The
||| conversions between a value and its object's address are this module's,
||| so these are not inlined.
export
valueObject : Flat.Uniform a -> Heap.Op Heap (Addr s)
valueObject v = do
  w <- intrinsic__valueWord v
  tag <- pointerTag
  Heap.pure (MkAddr (w - tag))

export
objectValue : Addr s -> Heap.Op Heap (Flat.Uniform a)
objectValue a = do
  tag <- pointerTag
  intrinsic__wordValue (a.word + tag)

||| The address of the object a pointer word in a field points to, and the
||| pointer word of an address, to store in a field.
export
fieldObject : (word : Bits64) -> Heap.Op Heap (Addr s)
fieldObject w = do
  tag <- pointerTag
  Heap.pure (MkAddr (w - tag))

export
fieldPointer : Addr s -> Heap.Op Heap Bits64
fieldPointer a = do
  tag <- pointerTag
  Heap.pure (a.word + tag)

||| A fixnum's integer, and the fixnum of a small integer, as a field holds
||| them: under both encodings with fixnums the integer is the word shifted
||| left by one, with the fixnum tag, the pointer tag's complement, below.
export
fixnumOf : (word : Bits64) -> Bits64
fixnumOf w = Bits.shiftR w 1

export
fixnumWord : Bits64 -> Heap.Op Heap Bits64
fixnumWord n = do
  tag <- pointerTag
  Heap.pure (Bits.shiftL n 1 + (1 - tag))

------------------------------------------------------------------------------
-- The system's memory

||| `x` rounded up to a whole number of the system's pages, what it commits
||| and releases by.
export
roundToPage : Bits64 -> Heap.Op Heap Bits64
roundToPage x = do
  page <- OS.osPageBytes
  Heap.pure ((x + (page - 1)) .&. (0 - page))

||| `bytes` of address space reserved, not yet usable; 0 if the system has
||| no such range.
export %inline
reserveMemory : (bytes : Bits64) -> Heap.Op Heap Bits64
reserveMemory = OS.osReserve

||| Memory committed to `bytes` of a reserved range from `addr`, both whole
||| pages: readable, writable and zero. The program ends if the system has
||| none.
export
commitMemory : (addr, bytes : Bits64) -> Heap.Op Heap ()
commitMemory addr bytes = do
  ok <- OS.osCommit addr bytes
  -- lint: allow trust-escape: memory the system refuses ends the program, which returns nothing
  if ok == 1 then Heap.pure () else assert_total (idris_crash "idris: cannot map memory")

||| Memory given back from `bytes` of a committed range from `addr`, both
||| whole pages, and the range reserved again.
export %inline
releaseMemory : (addr, bytes : Bits64) -> Heap.Op Heap ()
releaseMemory = OS.osRelease

||| `bytes` of fresh memory, zeroed, readable and writable, at an address the
||| system chooses; the program ends if the system has none.
export
mapMemory : (bytes : Bits64) -> Heap.Op Heap (Addr s)
mapMemory bytes = do
  whole <- roundToPage bytes
  a <- OS.osReserve whole
  ok <- if a == 0 then Heap.pure 0 else OS.osCommit a whole
  -- lint: allow trust-escape: memory the system refuses ends the program, which returns nothing
  if ok == 0
     then assert_total (idris_crash "idris: cannot map memory")
     else Heap.pure (MkAddr a)
