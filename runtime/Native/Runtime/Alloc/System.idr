||| The system's memory as an allocator's page source (`Pages Ordo`), and
||| the process's allocator of memory outside the heap: the size classes
||| over the buddy allocator of one arena of the default configuration,
||| made by the first allocation, its address in the runtime's state.
|||
||| The page source keeps addresses as words, as `Pages` holds them; this
||| module makes them the byte addresses the system takes.
module Native.Runtime.Alloc.System

import Native.Runtime.Alloc.Allocator
import Native.Runtime.Alloc.Arena
import Native.Runtime.Alloc.Chunks
import Native.Runtime.Alloc.Config
import Native.Runtime.Alloc.Pages
import Native.Runtime.Alloc.SizeClasses

import Native.Runtime.ByteAddr
import Native.Runtime.Cell
import Native.Runtime.Memory
import Native.Runtime.Ordo
import Native.Runtime.OS
import Native.Runtime.State

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

export
Pages Ordo where
  reserve bytes = do
    r <- OS.osReserve bytes
    Ordo.pure (ByteAddr.toWord r)
  commit addr bytes = do
    ok <- OS.osCommit (ByteAddr.fromWord addr) bytes
    Ordo.pure (ok == 1)
  release addr bytes = OS.osRelease (ByteAddr.fromWord addr) bytes
  pageBytes = OS.osPageBytes
  load addr off = Memory.loadAt (ByteAddr.fromWord addr) off
  store addr off v = Memory.storeAt (ByteAddr.fromWord addr) off v

||| The process's allocator, its arena made if it is not yet: the program
||| ends if the system has not the address space for it.
export
processAllocator : Ordo.Op Ordo (SizeClasses Chunks.Buddy)
processAllocator = do
  r <- State.getState State.foreignArena
  a <- if not (ByteAddr.isNull r) then Ordo.pure (ByteAddr.toWord r) else do
    n <- Arena.newArena {h = Ordo} Config.defaultConfig
    if n == 0 then Ordo.crashOp "idris: no address space for the allocator" else do
      State.setState State.foreignArena (ByteAddr.fromWord n)
      Ordo.pure n
  Ordo.pure (MkSizeClasses Config.defaultConfig a (Chunks.MkBuddy Config.defaultConfig a))

%cg native flat Runtime.Alloc.System.allocateBlock
||| A block of the process's allocator, and one given back.
export covering
allocateBlock : (bytes : Bits64) -> Ordo.Op Ordo Bits64
allocateBlock bytes = do
  s <- processAllocator
  Allocator.allocate s bytes

%cg native flat Runtime.Alloc.System.freeBlock
export covering
freeBlock : (addr : Bits64) -> Ordo.Op Ordo ()
freeBlock addr = do
  s <- processAllocator
  Allocator.free s addr
