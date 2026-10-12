||| Memory: addresses, and the reads and writes at them.
|||
||| An address is a word. This module is the only one that makes one from a
||| word or takes one apart: elsewhere an address comes only from an
||| operation that returns one, so no other word is used as an address by
||| mistake. Every access is at an address plus a byte offset, and threads
||| the token, so that accesses happen in the order the code gives them.
module Runtime.Memory

-- lint: allow public-import: the flat translation reaches through this module
-- (checking an importer's flat functions, it reaches this module's bodies,
-- which use it, so it is loaded wherever this module is)
import public Runtime.OS

import Compiler.Native.HeapObject
import Flat.Uniform
-- the runtime's own, never re-exported: each module that uses it imports it
import Runtime.Bits
import Runtime.Heap

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| The address of an object of kind `k`, or of memory the runtime maps.
export
record Addr (0 k : Kind) where
  constructor MkAddr
  word : Bits64

%extern prim__load64 : (base, offset : Bits64) -> (1 m : Heap) -> Ret Heap Bits64
%extern prim__load32 : (base, offset : Bits64) -> (1 m : Heap) -> Ret Heap Bits64
%extern prim__load16 : (base, offset : Bits64) -> (1 m : Heap) -> Ret Heap Bits64
%extern prim__load8 : (base, offset : Bits64) -> (1 m : Heap) -> Ret Heap Bits64
%extern prim__store64 : (base, offset, value : Bits64) -> (1 m : Heap) -> Ret Heap ()
%extern prim__store32 : (base, offset, value : Bits64) -> (1 m : Heap) -> Ret Heap ()
%extern prim__store16 : (base, offset, value : Bits64) -> (1 m : Heap) -> Ret Heap ()
%extern prim__store8 : (base, offset, value : Bits64) -> (1 m : Heap) -> Ret Heap ()

||| The word at the address plus the offset.
export %inline
load64 : Addr k -> (offset : Bits64) -> Op Heap Bits64
load64 a = prim__load64 a.word

||| The 32, 16 or 8 bits at the address plus the offset, as a word.
export %inline
load32, load16, load8 : Addr k -> (offset : Bits64) -> Op Heap Bits64
load32 a = prim__load32 a.word
load16 a = prim__load16 a.word
load8 a = prim__load8 a.word

||| Store the word at the address plus the offset.
export %inline
store64 : Addr k -> (offset, value : Bits64) -> Op Heap ()
store64 a = prim__store64 a.word

||| Store the word's low 32, 16 or 8 bits at the address plus the offset.
export %inline
store32, store16, store8 : Addr k -> (offset, value : Bits64) -> Op Heap ()
store32 a = prim__store32 a.word
store16 a = prim__store16 a.word
store8 a = prim__store8 a.word

------------------------------------------------------------------------------
-- Words as addresses, for the module that manages the spaces

||| The address a word is: for the modules that lay out the heap's spaces
||| and its objects, which compute addresses as words.
export %inline
fromWord : Bits64 -> Addr k
fromWord = MkAddr

||| The word an address is.
export %inline
toWord : Addr k -> Bits64
toWord a = a.word

||| The word at an address plus a byte offset, both words, and storing one:
||| the loads and stores for code that works on addresses as words.
export %inline
loadAt : (base, offset : Bits64) -> Op Heap Bits64
loadAt = prim__load64

export %inline
storeAt : (base, offset, value : Bits64) -> Op Heap ()
storeAt = prim__store64

------------------------------------------------------------------------------
-- The pinned registers, the encoding, the areas

%extern prim__getHp : (1 m : Heap) -> Ret Heap Bits64
%extern prim__setHp : (hp : Bits64) -> (1 m : Heap) -> Ret Heap ()
%extern prim__getHpLim : (1 m : Heap) -> Ret Heap Bits64
%extern prim__setHpLim : (hplim : Bits64) -> (1 m : Heap) -> Ret Heap ()
%extern prim__getK : (1 m : Heap) -> Ret Heap Bits64
%extern prim__setK : (k : Bits64) -> (1 m : Heap) -> Ret Heap ()
%extern prim__pointerTag : (1 m : Heap) -> Ret Heap Bits64
%extern prim__stackLimitArea : (1 m : Heap) -> Ret Heap Bits64
%extern prim__argvArea : (1 m : Heap) -> Ret Heap Bits64
%extern prim__rootsArea : (1 m : Heap) -> Ret Heap Bits64
%extern prim__nrootsArea : (1 m : Heap) -> Ret Heap Bits64
%extern prim__runtimeArea : (1 m : Heap) -> Ret Heap Bits64

||| The allocation window: inline allocation bumps the allocation pointer
||| until the limit, and takes the slow path past it.
export %inline
allocationPointer : Op Heap Bits64
allocationPointer = prim__getHp

export %inline
allocationLimit : Op Heap Bits64
allocationLimit = prim__getHpLim

export %inline
setAllocation : (hp, hplim : Bits64) -> Op Heap ()
setAllocation hp hplim = do
  prim__setHp hp
  prim__setHpLim hplim

||| Make `bytes` at the address the allocation window.
export
setWindow : Addr k -> (bytes : Bits64) -> Op Heap ()
setWindow a bytes = setAllocation a.word (a.word + bytes)

||| The current continuation, as the pointer word it is, and setting it:
||| the collector's first root, which it rewrites when it moves the
||| continuation. The conversions between the continuation and its word are
||| this module's, so these are not inlined into their callers.
export
continuation : Op Heap Bits64
continuation = prim__getK

export
setContinuation : Bits64 -> Op Heap ()
setContinuation = prim__setK

||| The pointer tag of the program's encoding: a pointer word is the
||| object's address plus the tag, and a word is a pointer exactly when its
||| low bit is the tag's. The runtime's one knowledge of the encoding.
export %inline
pointerTag : Op Heap Bits64
pointerTag = prim__pointerTag

||| The per-thread areas, as addresses: the word that holds the lowest the
||| machine stack pointer may go in direct code; the word that holds the
||| stack pointer at the program's entry, where the argument count, the
||| arguments' addresses and the environment's are; the root buffer and the
||| word that counts its entries in use; and the runtime's state.
export
stackLimitArea : Op Heap (Addr k)
stackLimitArea = do
  w <- prim__stackLimitArea
  pure (MkAddr w)

export
argvArea : Op Heap (Addr k)
argvArea = do
  w <- prim__argvArea
  pure (MkAddr w)

export %inline
rootsArea : Op Heap Bits64
rootsArea = prim__rootsArea

export %inline
nrootsArea : Op Heap Bits64
nrootsArea = prim__nrootsArea

export %inline
runtimeArea : Op Heap Bits64
runtimeArea = prim__runtimeArea

------------------------------------------------------------------------------
-- Values as ordinary code holds them, and the objects they point to

%extern prim__stringWord : Uniform String -> (1 m : Heap) -> Ret Heap Bits64
%extern prim__wordString : Bits64 -> (1 m : Heap) -> Ret Heap (Uniform String)
%extern prim__conWord : {0 a : Type} -> Uniform a -> (1 m : Heap) -> Ret Heap Bits64
%extern prim__wordCon : {0 a : Type} -> Bits64 -> (1 m : Heap) -> Ret Heap (Uniform a)

||| The object a string is, and the string an object is. A string is always
||| an object, so these never test the word. The conversions between a value
||| and its object's address are this module's, so these are not inlined.
export
stringObject : Uniform String -> Op Heap (Addr STRING)
stringObject s = do
  w <- prim__stringWord s
  tag <- pointerTag
  pure (MkAddr (w - tag))

export
stringValue : Addr STRING -> Op Heap (Uniform String)
stringValue a = do
  tag <- pointerTag
  prim__wordString (a.word + tag)

||| The object a value of a data type is, and the value an object is: for a
||| type whose values ordinary code holds as objects always, such as a list,
||| whose `[]` is a static object.
export
conObject : Uniform a -> Op Heap (Addr CON)
conObject v = do
  w <- prim__conWord v
  tag <- pointerTag
  pure (MkAddr (w - tag))

export
conValue : Addr CON -> Op Heap (Uniform a)
conValue a = do
  tag <- pointerTag
  prim__wordCon (a.word + tag)

||| The address of the object a pointer word in a field points to, and the
||| pointer word of an address, to store in a field.
export
fieldObject : (word : Bits64) -> Op Heap (Addr k)
fieldObject w = do
  tag <- pointerTag
  pure (MkAddr (w - tag))

export
fieldPointer : Addr k -> Op Heap Bits64
fieldPointer a = do
  tag <- pointerTag
  pure (a.word + tag)

||| A fixnum's integer, and the fixnum of a small integer, as a field holds
||| them: under both encodings with fixnums the integer is the word shifted
||| left by one, with the fixnum tag, the pointer tag's complement, below.
export
fixnumOf : (word : Bits64) -> Bits64
fixnumOf w = shiftR w 1

export
fixnumWord : Bits64 -> Op Heap Bits64
fixnumWord n = do
  tag <- pointerTag
  pure (shiftL n 1 + (1 - tag))

------------------------------------------------------------------------------
-- The system's memory

||| `x` rounded up to a whole number of the system's pages, what it commits
||| and releases by.
export
roundToPage : Bits64 -> Op Heap Bits64
roundToPage x = do
  page <- osPageBytes
  pure ((x + (page - 1)) .&. (0 - page))

||| `bytes` of address space reserved, not yet usable; 0 if the system has
||| no such range.
export %inline
reserveMemory : (bytes : Bits64) -> Op Heap Bits64
reserveMemory = osReserve

||| Memory committed to `bytes` of a reserved range from `addr`, both whole
||| pages: readable, writable and zero. The program ends if the system has
||| none.
export
commitMemory : (addr, bytes : Bits64) -> Op Heap ()
commitMemory addr bytes = do
  ok <- osCommit addr bytes
  -- lint: allow trust-escape: memory the system refuses ends the program, which returns nothing
  if ok == 1 then pure () else assert_total (idris_crash "idris: cannot map memory")

||| Memory given back from `bytes` of a committed range from `addr`, both
||| whole pages, and the range reserved again.
export %inline
releaseMemory : (addr, bytes : Bits64) -> Op Heap ()
releaseMemory = osRelease

||| `bytes` of fresh memory, zeroed, readable and writable, at an address the
||| system chooses; the program ends if the system has none.
export
mapMemory : (bytes : Bits64) -> Op Heap (Addr k)
mapMemory bytes = do
  whole <- roundToPage bytes
  a <- osReserve whole
  ok <- if a == 0 then pure 0 else osCommit a whole
  -- lint: allow trust-escape: memory the system refuses ends the program, which returns nothing
  if ok == 0
     then assert_total (idris_crash "idris: cannot map memory")
     else pure (MkAddr a)
