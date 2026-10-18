||| The system's memory as an allocator's page source (`Pages Heap`), and
||| the process's allocator of memory outside the heap: the size classes
||| over the buddy allocator of one arena of the default configuration,
||| made by the first allocation, its address in the runtime's state.
|||
||| The page source keeps addresses as words, as `Pages` holds them; this
||| module makes them the raw addresses the system takes.
module Native.Runtime.Alloc.System

import Native.Runtime.Alloc.Allocator
import Native.Runtime.Alloc.Arena
import Native.Runtime.Alloc.Chunks
import Native.Runtime.Alloc.Config
import Native.Runtime.Alloc.Pages
import Native.Runtime.Alloc.SizeClasses
-- lint: allow import-unused: the flat check reaches through the allocator's bodies, which use the word operations
import Native.Runtime.Bits
import Native.Runtime.Heap
import Native.Runtime.Memory
import Native.Runtime.OS
import Native.Runtime.Raw
import Native.Runtime.State

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

export
Pages Heap where
  reserve bytes = do
    r <- OS.osReserve bytes
    Heap.pure (Raw.rawWord r)
  commit addr bytes = do
    ok <- OS.osCommit (Raw.fromWord addr) bytes
    Heap.pure (ok == 1)
  release addr bytes = OS.osRelease (Raw.fromWord addr) bytes
  pageBytes = OS.osPageBytes
  load addr off = Memory.loadAt (Raw.fromWord addr) off
  store addr off v = Memory.storeAt (Raw.fromWord addr) off v

||| The process's allocator, its arena made if it is not yet: the program
||| ends if the system has not the address space for it.
export
processAllocator : Heap.Op Heap (SizeClasses Buddy)
processAllocator = do
  r <- State.getState State.foreignArena
  a <- if not (Raw.isNull r) then Heap.pure (Raw.rawWord r) else do
    n <- Arena.newArena {h = Heap} Config.defaultConfig
    if n == 0 then Heap.crashOp "idris: no address space for the allocator" else do
      State.setState State.foreignArena (Raw.fromWord n)
      Heap.pure n
  Heap.pure (MkSizeClasses Config.defaultConfig a (MkBuddy Config.defaultConfig a))

%cg native flat Runtime.Alloc.System.allocateBlock
||| A block of the process's allocator, and one given back.
export covering
allocateBlock : (bytes : Bits64) -> Heap.Op Heap Bits64
allocateBlock bytes = do
  s <- processAllocator
  Allocator.allocate s bytes

%cg native flat Runtime.Alloc.System.freeBlock
export covering
freeBlock : (addr : Bits64) -> Heap.Op Heap ()
freeBlock addr = do
  s <- processAllocator
  Allocator.free s addr
