||| The foreign functions of `base`'s `System.Directory`, as the runtime
||| implements them, through the OS services, each a flat function of the
||| foreign one's name and type (`Native.Support.Foreign.System` says how
||| they are bound). Those that take a path are the string module's, which
||| reads it.
module Native.Support.Foreign.System.Directory

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
import Native.Runtime.OS
-- lint: allow import-unused: the flat check reaches through the allocator's bodies, which use raw memory
import Native.Runtime.Raw as Runtime
-- lint: allow import-unused: the flat check reaches through newPtr's body, which allocates the pointer's object
import Native.Runtime.Space
-- lint: allow import-unused: the flat check reaches through newPtr's body, which writes the pointer's header
import Native.Support.Obj
import Native.Support.Ptr
-- lint: allow import-unused: the flat check reaches through newPtr's body, which writes the pointer's header
import Native.Types.Header
-- lint: allow import-unused: the flat check reaches through newPtr's body, which writes the pointer's header
import Native.Types.Kind

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

%cg native flat Support.Foreign.System.Directory.prim__currentDir
||| `currentDir`: a pointer to the current directory's path, zero-ended, in
||| a new block outside the heap, which `base`'s `currentDir` frees once it
||| has copied the path (`System.FFI.free`, bound to
||| `Support.Foreign.System.FFI.prim__free`); the null pointer if there is
||| no memory, or the path is longer than the block, `pathBytes`, as the C
||| support's buffer is.
export covering
prim__currentDir : PrimIO (Flat.Uniform (Ptr String))
prim__currentDir w = let (Runtime.MkOrdo # r) = currentOp Runtime.MkOrdo in MkIORes r w
  where
    ||| The most bytes of a path, its zero byte one: Linux's `PATH_MAX`.
    pathBytes : Bits64
    pathBytes = 4096

    covering
    currentOp : Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform (Ptr String))
    currentOp = Runtime.Alloc.Block.allocate pathBytes (Ptr.newPtr 0) (\b => do
      let MkAddressed p b' = Runtime.Alloc.Block.address b
      ok <- Runtime.OS.osCurrentDirectory p pathBytes
      case ok == 1 of
        -- lint: allow sealed-allocator: base's `System.Directory.currentDir` frees the block
        -- (`free $ prim__forgetPtr res`, our `prim__free`) once `prim__getString` has copied the path
        True => do
          a <- Runtime.Alloc.Block.releaseBlock b'
          Ptr.newPtr (Runtime.Raw.rawWord a)
        False => do
          Runtime.Alloc.Block.free b'
          Ptr.newPtr 0)
