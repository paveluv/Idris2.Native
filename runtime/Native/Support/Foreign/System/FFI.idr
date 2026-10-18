||| The foreign functions of `base`'s `System.FFI`, as the runtime implements
||| them: `malloc` and `free` over the process's allocator of memory outside
||| the heap (`Native.Runtime.Alloc.Block`), each a flat function of the
||| foreign one's name and type (`Native.Support.Foreign.System` says how
||| they are bound). A block is a pointer as ordinary code holds one
||| (`Native.Support.Ptr`).
module Native.Support.Foreign.System.FFI

import Native.Flat.Uniform as Flat
-- lint: allow import-unused: the flat check reaches through newPtr's body, whose header has a shape
import Native.HeapObj.Shape as HeapObj
-- lint: allow import-unused: the flat check reaches through the allocator's bodies, which hold its records
import Native.Runtime.Alloc.Allocator
import Native.Runtime.Alloc.Arena
import Native.Runtime.Alloc.Block
import Native.Runtime.Alloc.Chunks
import Native.Runtime.Alloc.Config
import Native.Runtime.Alloc.Pages
import Native.Runtime.Alloc.SizeClasses
import Native.Runtime.Alloc.System
-- lint: allow import-unused: the flat check reaches through the allocator's bodies, which use the word operations
import Native.Runtime.Bits
import Native.Runtime.Memory
import Native.Runtime.Ordo as Runtime
import Native.Runtime.Raw as Runtime
-- lint: allow import-unused: the flat check reaches through newPtr's body, which allocates the pointer's object
import Native.Runtime.Space
-- lint: allow import-unused: the flat check reaches through pointee's body, which reads the pointer's object
import Native.Support.Obj
import Native.Support.Ptr
-- lint: allow import-unused: the flat check reaches through newPtr's body, which writes the pointer's header
import Native.Types.Header
import Native.Types.Kind
import Native.Types.Represents

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

%cg native flat Support.Foreign.System.FFI.prim__malloc
||| `malloc`: a block of at least `size` bytes, aligned to 16, its contents
||| unspecified; the null pointer if there is no memory for it, or for a
||| negative size, which C's `size_t` would take for a huge one.
export covering
prim__malloc : Int -> PrimIO (Flat.Uniform AnyPtr)
prim__malloc size w = let (Runtime.MkOrdo # r) = mallocOp size Runtime.MkOrdo in MkIORes r w
  where
    covering
    mallocOp : Int -> Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform AnyPtr)
    mallocOp n = if n < 0 then Ptr.nullPtr else
      -- lint: allow sealed-allocator: the program owns the block, and frees it with `free`
      Runtime.Alloc.Block.allocate (cast n) (Ptr.nullPtr) (\b => do
        a <- Runtime.Alloc.Block.releaseBlock b
        Ptr.newPtr a)

%cg native flat Support.Foreign.System.FFI.prim__free
||| `free`: a block `malloc` gave back; the null pointer is no block. An
||| address `malloc` did not give ends the program. A pointer that is an
||| object of the heap (`Support.Ptr`), which `base` frees once it has read
||| it, is the collector's, and freeing it does nothing.
export covering
prim__free : Flat.Uniform AnyPtr -> PrimIO ()
prim__free p w = let (Runtime.MkOrdo # ()) = freeOp p Runtime.MkOrdo in MkIORes () w
  where
    covering
    freeOp : Flat.Uniform AnyPtr -> Runtime.Ordo.Op Runtime.Ordo ()
    freeOp p = do
      target <- Ptr.pointee p
      case target of
        Address a =>
          if Runtime.Raw.isNull a then Runtime.Ordo.pure () else
            -- lint: allow sealed-allocator: an address the program gives back, as C's free takes one; the allocator ends the program for one it did not give
            Runtime.Alloc.Block.free (Runtime.Alloc.Block.adoptBlock a)
        -- the collector keeps an object of the heap given for a pointer
        HeapString _ => Runtime.Ordo.pure ()
