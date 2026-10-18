-- The allocator on the system's memory, natively: the driver (`Driver`)
-- over the process's allocator, with its default configuration, blocks of
-- up to 64 KiB in slabs and larger ones up to 2.6 MiB as chunks. A load or a
-- store into memory the allocator did not commit would end the program; a
-- block that overlaps another, or whose tags another write changed, is
-- counted.
--
-- The allocator's operations are flat functions over the heap token, and a
-- program calls flat code through the boundary from ordinary code: each
-- operation here is a flat function of an `IO` type, which runs the
-- operation on the token, as the runtime's own `IO` primitives do:
--
--     nativeAlloc n = primIO (\w => let (MkHeap # a) = allocateBlock n MkHeap in MkIORes a w)
module Main

import Driver
import Native.Runtime.Alloc.Allocator
import Native.Runtime.Alloc.Arena
import Native.Runtime.Alloc.Chunks
import Native.Runtime.Alloc.Config
import Native.Runtime.Alloc.Pages
import Native.Runtime.Alloc.SizeClasses
import Native.Runtime.Alloc.System
import Native.Runtime.Bits
import Native.Runtime.Heap
import Native.Runtime.Memory
import Native.Runtime.Raw
import Native.Runtime.State

%default covering

%cg native flat Main.nativeAlloc Main.nativeFree Main.nativeLoad Main.nativeStore

nativeAlloc : Bits64 -> IO Bits64
nativeAlloc n = primIO $ \w => let (MkHeap # a) = allocateBlock n MkHeap in MkIORes a w

nativeFree : Bits64 -> IO ()
nativeFree a = primIO $ \w => let (MkHeap # ()) = freeBlock a MkHeap in MkIORes () w

nativeLoad : Bits64 -> IO Bits64
nativeLoad a = primIO $ \w => let (MkHeap # v) = Memory.loadAt (Raw.fromWord a) 0 MkHeap in MkIORes v w

nativeStore : Bits64 -> Bits64 -> IO ()
nativeStore a v = primIO $ \w => let (MkHeap # ()) = Memory.storeAt (Raw.fromWord a) 0 v MkHeap in MkIORes () w

main : IO ()
main = do
  t <- run (MkOps nativeAlloc nativeFree nativeLoad nativeStore) 65536 7 20000
  putStrLn ("native: " ++ show t)
