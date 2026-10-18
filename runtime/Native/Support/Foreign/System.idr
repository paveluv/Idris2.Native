||| The foreign functions of `base`'s `System`, as the runtime implements
||| them: each a flat function of the foreign one's name and type, which the
||| native code generator binds it to (`foreignFunctions`), so that ordinary
||| code calls it through the boundary, which converts its arguments and its
||| result as their types say.
module Native.Support.Foreign.System

import Native.Flat.Uniform as Flat
-- lint: allow import-unused: the flat check reaches through newPtr's body and the environment's, which allocate
import Native.HeapObj.Shape as HeapObj
import Native.Runtime.Alloc.Allocator
import Native.Runtime.Alloc.Arena
import Native.Runtime.Alloc.Chunks
import Native.Runtime.Alloc.Config
import Native.Runtime.Alloc.Pages
import Native.Runtime.Alloc.SizeClasses
import Native.Runtime.Alloc.System
import Native.Runtime.Bits
import Native.Runtime.Heap as Runtime
import Native.Runtime.Memory
-- lint: allow import-unused: the flat check reaches through argumentCount's body, which uses raw memory
import Native.Runtime.Raw as Runtime
import Native.Runtime.Space
import Native.Runtime.State
import Native.Runtime.System
import Native.Support.Environment
import Native.Support.Obj
import Native.Support.Ptr
import Native.Types.Header
import Native.Types.Kind

%default total

%cg native flat Support.Foreign.System.prim__exit
||| End the process with the status: its low byte is what the parent sees.
export
prim__exit : Int -> PrimIO ()
prim__exit status w = let (Runtime.MkHeap # ()) = Runtime.System.exit (cast status) Runtime.MkHeap in MkIORes () w

%cg native flat Support.Foreign.System.prim__getArgCount
||| How many arguments the program has, its name the first, as the system
||| gave them.
export
prim__getArgCount : PrimIO Int
prim__getArgCount w = let (Runtime.MkHeap # n) = Runtime.Memory.argumentCount Runtime.MkHeap in MkIORes (cast n) w

%cg native flat Support.Foreign.System.prim__getEnvPair
||| `getEnvironment`'s entry `n` of the environment (`Support.Environment`):
||| a pointer to its bytes, `NAME=value`; the null pointer past the last.
export covering
prim__getEnvPair : Int -> PrimIO (Flat.Uniform (Ptr String))
prim__getEnvPair n w = let (Runtime.MkHeap # r) = pairOp n Runtime.MkHeap in MkIORes r w
  where
    covering
    pairOp : Int -> Runtime.Heap.Op Runtime.Heap (Flat.Uniform (Ptr String))
    pairOp n = if n < 0 then Ptr.newPtr 0 else do
      e <- Environment.entryAt (cast n)
      Ptr.newPtr e
