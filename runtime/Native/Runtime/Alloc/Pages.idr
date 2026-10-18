||| What an allocator of memory outside the heap needs from the system
||| (`Pages`): address space reserved, pages committed in it and given back,
||| and the words of what it commits. An allocator is written once against
||| this interface, so that it runs against the system's memory
||| (`Alloc.System`) and against a model, where a test checks it.
|||
||| Addresses are words here, as the collector's interface holds them: the
||| allocator computes with them, and an instance makes them the addresses
||| its memory is reached by.
module Native.Runtime.Alloc.Pages

import Native.Runtime.Heap

%default total

public export
interface Pages (0 h : Type) where
  ||| `bytes` of address space reserved, whole pages, neither readable nor
  ||| writable; its address, 0 if the system has none.
  reserve : (bytes : Bits64) -> Heap.Op h Bits64
  ||| `bytes` of reserved whole pages from the address made readable,
  ||| writable and zero; whether the system had the memory.
  commit : (addr, bytes : Bits64) -> Heap.Op h Bool
  ||| `bytes` of committed whole pages from the address given back, and
  ||| reserved again: they read as zero once committed anew.
  release : (addr, bytes : Bits64) -> Heap.Op h ()
  ||| The system's page, what it reserves, commits and releases by.
  pageBytes : Heap.Op h Bits64
  ||| The word at the address plus a byte offset, in committed memory, and
  ||| storing one.
  load : (addr, offset : Bits64) -> Heap.Op h Bits64
  store : (addr, offset, value : Bits64) -> Heap.Op h ()
