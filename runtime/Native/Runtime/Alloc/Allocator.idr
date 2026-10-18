||| An allocator of memory outside the heap (`Allocator`): memory that the
||| collector never moves or scans, given back explicitly, for what the
||| system, C's conventions or a program keep a pointer to across calls.
||| The runtime's is the size classes over the buddy allocator of one arena
||| (`Alloc.SizeClasses`); another (a bump arena given back at once, a pool
||| of one size, a library's own) is another instance.
|||
||| No heap value is ever stored in such memory: the collector does not see
||| it, and would move or free what it points to.
module Native.Runtime.Alloc.Allocator

import Native.Runtime.Heap

%default total

public export
interface Allocator (0 h : Type) (0 a : Type) where
  ||| A block of `bytes` at least, aligned to 16 bytes, its contents
  ||| unspecified: its address, 0 if there is no memory for it.
  allocate : a -> (bytes : Bits64) -> Heap.Op h Bits64
  ||| A block given back, by the address `allocate` gave; 0 is no block, and
  ||| gives back nothing. An address this allocator did not give ends the
  ||| program.
  free : a -> (addr : Bits64) -> Heap.Op h ()
