||| The foreign functions of `base`'s `System.FFI`, as the system tier
||| implements them: `malloc` and `free` over the process's allocator of
||| memory outside the heap (`Native.Runtime.Alloc.Block`), each a flat
||| function of the foreign one's name and type (`Native.System` says how
||| they are bound). A block is a pointer as ordinary code holds one
||| (`Native.Support.Ptr`).
module Native.System.Foreign.System.FFI

import Native.Flat.Uniform as Flat
import Native.Runtime.Alloc.Block as Runtime.Alloc
import Native.Runtime.ByteAddr as Runtime
import Native.Runtime.Ordo as Runtime
import Native.Support.Ptr
import Native.Types.Represents

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

%cg native flat System.Foreign.System.FFI.prim__malloc
||| `malloc`: a block of at least `size` bytes, aligned to 16, its contents
||| unspecified; the null pointer if there is no memory for it, or for a
||| negative size, which C's `size_t` would take for a huge one.
export covering
prim__malloc : Int -> PrimIO (Flat.Uniform AnyPtr)
prim__malloc size w = let (Runtime.MkOrdo # r) = mallocOp size Runtime.MkOrdo in MkIORes r w
  where
    covering
    mallocOp : Int -> Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform AnyPtr)
    mallocOp n = if n < 0 then Support.Ptr.nullPtr else
      -- lint: allow sealed-allocator: the program owns the block, and frees it with `free`
      Runtime.Alloc.Block.allocate (cast n) (Support.Ptr.nullPtr) (\b => do
        a <- Runtime.Alloc.Block.releaseBlock b
        Support.Ptr.newPtr a)

%cg native flat System.Foreign.System.FFI.prim__free
||| `free`: a block `malloc` gave back; the null pointer is no block. An
||| address `malloc` did not give ends the program. A pointer that is an
||| object of the heap (`Support.Ptr`), which `base` frees once it has read
||| it, is the collector's, and freeing it does nothing, as freeing a handle
||| does, which the system tier closes.
export covering
prim__free : Flat.Uniform AnyPtr -> PrimIO ()
prim__free p w = let (Runtime.MkOrdo # ()) = freeOp p Runtime.MkOrdo in MkIORes () w
  where
    covering
    freeOp : Flat.Uniform AnyPtr -> Runtime.Ordo.Op Runtime.Ordo ()
    freeOp p = do
      target <- Support.Ptr.pointee p
      case target of
        Support.Ptr.Address a =>
          if Runtime.ByteAddr.isNull a then Runtime.Ordo.pure () else
            -- lint: allow sealed-allocator: an address the program gives back, as C's free takes
            -- one; the allocator ends the program for one it did not give
            Runtime.Alloc.Block.free (Runtime.Alloc.Block.adoptBlock a)
        -- the collector keeps an object of the heap given for a pointer
        Support.Ptr.HeapString _ => Runtime.Ordo.pure ()
        -- a handle is the system tier's to close, by its own functions
        Support.Ptr.Handle _ => Runtime.Ordo.pure ()
