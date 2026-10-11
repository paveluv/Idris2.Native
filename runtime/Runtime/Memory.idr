||| Memory: addresses, and the reads and writes at them.
|||
||| An address is a word. This module is the only one that makes one from a
||| word or takes one apart: elsewhere an address comes only from an
||| operation that returns one, so no other word is used as an address by
||| mistake. Every access is at an address plus a byte offset, and threads
||| the token, so that accesses happen in the order the code gives them.
module Runtime.Memory

-- public, so that a module importing this one has the definitions the flat
-- translation reaches through it, as it checks that module's flat functions
import public Compiler.Native.HeapObject
import public Runtime.Heap
import public Runtime.System

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

||| `bytes` of fresh memory, zeroed, readable and writable, at an address the
||| system chooses; the program ends if the system has none.
export
mapMemory : (bytes : Bits64) -> Op Heap (Addr k)
mapMemory bytes = do
  -- mmap(NULL, bytes, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0)
  r <- syscall 9 0 bytes 3 0x22 0xFFFFFFFFFFFFFFFF 0
  -- an error is a negative number from -4095 to -1
  if r > 0xFFFFFFFFFFFFF000
     then assert_total (idris_crash "idris: cannot map memory")
     else pure (MkAddr r)

------------------------------------------------------------------------------
-- Words as addresses, for the module that manages the spaces

||| The address a word is. `Runtime.Space`, which manages the heap's spaces
||| and so sees addresses as words, is the one client meant.
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
-- The system's memory

||| Linux's page: what the system commits and releases by.
export
pageBytes : Bits64
pageBytes = 4096

||| `x` rounded up to a page.
export
roundToPage : Bits64 -> Bits64
roundToPage x = prim__and_Bits64 (x + (pageBytes - 1)) 0xFFFFFFFFFFFFF000

||| `bytes` of address space reserved, at an address the system chooses, and
||| not yet usable: no memory is committed to it, and no overcommit setting
||| counts it, until `commitMemory`. 0 if the system has no such range.
export
reserveMemory : (bytes : Bits64) -> Op Heap Bits64
reserveMemory bytes = do
  -- mmap(NULL, bytes, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0)
  r <- syscall 9 0 bytes 0 0x4022 0xFFFFFFFFFFFFFFFF 0
  pure (if r > 0xFFFFFFFFFFFFF000 then 0 else r)

||| Memory committed to `bytes` of a reserved range from `addr`, both whole
||| pages: readable, writable and zero. The program ends if the system has
||| none.
export
commitMemory : (addr, bytes : Bits64) -> Op Heap ()
commitMemory addr bytes = do
  -- mprotect(addr, bytes, PROT_READ | PROT_WRITE)
  r <- syscall 10 addr bytes 3 0 0 0
  if r == 0 then pure () else assert_total (idris_crash "idris: cannot map memory")

||| Memory given back from `bytes` of a committed range from `addr`, both
||| whole pages: released to the system, and the range reserved again as
||| `reserveMemory` left it.
export
releaseMemory : (addr, bytes : Bits64) -> Op Heap ()
releaseMemory addr bytes = do
  -- madvise(addr, bytes, MADV_DONTNEED); mprotect(addr, bytes, PROT_NONE)
  _ <- syscall 28 addr bytes 4 0 0 0
  _ <- syscall 10 addr bytes 0 0 0 0
  pure ()

||| The soft limit of the process's stack, in bytes, by getrlimit, which
||| writes it into the 16 bytes at `buffer`; `otherwise` if the system does
||| not say.
export
stackSoftLimit : (buffer : Addr k) -> (otherwise : Bits64) -> Op Heap Bits64
stackSoftLimit buffer otherwise = do
  store64 buffer 0 otherwise
  -- getrlimit(RLIMIT_STACK, buffer)
  _ <- syscall 97 3 buffer.word 0 0 0 0
  load64 buffer 0
