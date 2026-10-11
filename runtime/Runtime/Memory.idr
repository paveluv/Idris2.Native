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
