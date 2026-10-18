||| The foreign functions of `base`'s `System.Directory`, as the runtime
||| implements them, through the OS services, each a flat function of the
||| foreign one's name and type (`Native.Support.Foreign.System` says how
||| they are bound). A path is the system's text through `Support.Text`, for
||| every encoding.
module Native.Support.Foreign.System.Directory

-- lint: allow import-unused: the flat check reaches through withText's body, which records the failure of no memory
import Native.Failure
import Native.Flat.Uniform as Flat
-- lint: allow import-unused: the flat check reaches through pointee's body, which reads the pointer's object by its kind
import Native.HeapObj.Shape as HeapObj
-- lint: allow import-unused: the flat check reaches through withText's body, which copies a string into a block outside the heap
import Native.Runtime.Alloc.Allocator
-- lint: allow import-unused: the flat check reaches through withText's body, which copies a string into a block outside the heap
import Native.Runtime.Alloc.Arena
import Native.Runtime.Alloc.Block
-- lint: allow import-unused: the flat check reaches through withText's body, which copies a string into a block outside the heap
import Native.Runtime.Alloc.Chunks
-- lint: allow import-unused: the flat check reaches through withText's body, which copies a string into a block outside the heap
import Native.Runtime.Alloc.Config
-- lint: allow import-unused: the flat check reaches through withText's body, which copies a string into a block outside the heap
import Native.Runtime.Alloc.Pages
-- lint: allow import-unused: the flat check reaches through withText's body, which copies a string into a block outside the heap
import Native.Runtime.Alloc.SizeClasses
-- lint: allow import-unused: the flat check reaches through withText's body, which copies a string into a block outside the heap
import Native.Runtime.Alloc.System
-- lint: allow import-unused: the flat check reaches through the allocator's bodies, which use the word operations
import Native.Runtime.Bits
import Native.Runtime.Ordo as Runtime
import Native.Runtime.OS
import Native.Runtime.Raw as Runtime
-- lint: allow import-unused: the flat check reaches through newPtr's body, which allocates the pointer's object
import Native.Runtime.Space
-- lint: allow import-unused: the flat check reaches through withText's body, which records the failure of no memory
import Native.Runtime.State
-- lint: allow import-unused: the flat check reaches through pointee's body, which reads the pointer's object by its kind
import Native.Support.Obj
import Native.Support.Ptr
import Native.Support.Text
-- lint: allow import-unused: the flat check reaches through newPtr's body, which writes the pointer's header
import Native.Types.Header
-- lint: allow import-unused: the flat check reaches through pointee's body, which reads the pointer's object by its kind
import Native.Types.Kind
import Native.Types.Represents

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| An OS service of a path, called with the string as the system takes a
||| path (`Text.withPath`): 0 when it succeeds, -1 when it fails or there is
||| no memory for the path, as the C library's calls answer.
%inline covering
ofPath : (Runtime.Raw -> Runtime.Ordo.Op Runtime.Ordo Bits64) -> Flat.Uniform String -> Runtime.Ordo.Op Runtime.Ordo Int
ofPath service path = Text.withPath path (Runtime.Ordo.pure (-1)) (\p => do
  ok <- service p
  Runtime.Ordo.pure (if ok == 1 then 0 else -1))

%cg native flat Support.Foreign.System.Directory.prim__changeDir
||| `changeDir`: the directory of the path made the current one; 0 when it
||| is, -1 when it is not, as the C library's `chdir` answers.
export covering
prim__changeDir : Flat.Uniform String -> PrimIO Int
prim__changeDir path w = let (Runtime.MkOrdo # r) = ofPath Runtime.OS.osChangeDirectory path Runtime.MkOrdo in MkIORes r w

%cg native flat Support.Foreign.System.Directory.prim__createDir
||| `createDir`: a directory made at the path; 0 when it is, -1 when it is
||| not, as the C library's `mkdir` answers, the reason the last failure.
export covering
prim__createDir : Flat.Uniform String -> PrimIO Int
prim__createDir path w = let (Runtime.MkOrdo # r) = ofPath Runtime.OS.osCreateDirectory path Runtime.MkOrdo in MkIORes r w

%cg native flat Support.Foreign.System.Directory.prim__removeDir
||| `removeDir`: the empty directory at the path removed, if it can be, the
||| reason the last failure if not.
export covering
prim__removeDir : Flat.Uniform String -> PrimIO ()
prim__removeDir path w = let (Runtime.MkOrdo # _) = ofPath Runtime.OS.osRemoveDirectory path Runtime.MkOrdo in MkIORes () w

%cg native flat Support.Foreign.System.Directory.prim__currentDir
||| `currentDir`: the current directory's path, as the system writes it,
||| zero-ended, into a block outside the heap of `pathBytes`, copied into a
||| string given as the pointer (`Support.Ptr`), the block freed; the null
||| pointer if there is no memory, or the path is longer than the block, as
||| the C support's buffer is.
export covering
prim__currentDir : PrimIO (Flat.Uniform (Ptr String))
prim__currentDir w = let (Runtime.MkOrdo # r) = currentOp Runtime.MkOrdo in MkIORes r w
  where
    ||| The most bytes of a path, its zero byte one: Linux's `PATH_MAX`.
    pathBytes : Bits64
    pathBytes = 4096

    covering
    currentOp : Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform (Ptr String))
    currentOp = Runtime.Alloc.Block.allocate pathBytes Ptr.nullPtr (\b => do
      let MkAddressed p b' = Runtime.Alloc.Block.address b
      ok <- Runtime.OS.osCurrentDirectory p pathBytes
      case ok == 1 of
        True => do
          s <- Text.zeroEndedText p
          Runtime.Alloc.Block.free b'
          Ptr.stringPtr s
        False => do
          Runtime.Alloc.Block.free b'
          Ptr.nullPtr)
