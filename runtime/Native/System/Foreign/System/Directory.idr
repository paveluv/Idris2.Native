||| The foreign functions of `base`'s `System.Directory`, as the system tier
||| implements them, through the OS services: the current directory changed
||| and read, directories made and removed, each a flat function, and a
||| directory's entries listed, an open directory a file of the table
||| (`Native.System.File`) whose entries alone are read, each an ordinary
||| function; all of the foreign one's name and type (`Native.System` says
||| how they are bound). A path is the system's text through `Support.Text`,
||| for every encoding.
module Native.System.Foreign.System.Directory

import Native.Flat.Uniform as Flat
import Native.OpenFlag
import Native.Runtime.Alloc.Block as Runtime.Alloc
import Native.Runtime.ByteAddr as Runtime
import Native.Runtime.Ordo as Runtime
import Native.Runtime.OS
import Native.Support.Ptr
import Native.Support.Text
import Native.System.Call
import Native.System.File
import Native.Types.Represents

%default total

||| `openDir`: the directory at the path opened to read its entries; the
||| null pointer if it is not, the reason the last failure.
export covering
prim__openDir : String -> PrimIO AnyPtr
prim__openDir path = toPrim $ do
  h <- Call.openPath (Flat.MkUniform path)
         (prim__or_Bits64 (OpenFlag.bit OpenFlag.ForReading) (OpenFlag.bit OpenFlag.ADirectory))
  if h == Runtime.OS.failedWord then pure Call.nullPointer.value else do
    d <- File.newFile h
    File.register d

||| `nextDirEntry`: the directory's next entry's name, `.` and `..` among
||| them, as a string given as the pointer (`Support.Ptr`); the null
||| pointer when there are no more, or if the read fails, which `base` tells
||| apart by the last failure, 0 at the end, as the C support clears `errno`
||| first.
export covering
prim__dirEntry : AnyPtr -> PrimIO (Ptr String)
prim__dirEntry p = toPrim $ do
  Call.clearFailure
  File.withFile p Call.nullString.value (\_, d => do
    name <- Call.readEntry !(File.handle d)
    pure (if name.value == "" then Call.nullString.value
          else (Call.stringPointer name).value))

||| `closeDir`: the directory closed.
export covering
prim__closeDir : AnyPtr -> PrimIO ()
prim__closeDir p = toPrim $ File.withFile p () (\slot, d => do
  Call.close !(File.handle d)
  File.release slot)

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

||| An OS service of a path, called with the string as the system takes a
||| path (`Text.withPath`): 0 when it succeeds, -1 when it fails or there is
||| no memory for the path, as the C library's calls answer.
%inline covering
ofPath : (Runtime.ByteAddr -> Runtime.Ordo.Op Runtime.Ordo Bits64) -> Flat.Uniform String ->
         Runtime.Ordo.Op Runtime.Ordo Int
ofPath service path = Support.Text.withPath path (Runtime.Ordo.pure (-1)) (\p => do
  ok <- service p
  Runtime.Ordo.pure (if ok == 1 then 0 else -1))

%cg native flat System.Foreign.System.Directory.prim__changeDir
||| `changeDir`: the directory of the path made the current one; 0 when it
||| is, -1 when it is not, as the C library's `chdir` answers.
export covering
prim__changeDir : Flat.Uniform String -> PrimIO Int
prim__changeDir path w = let (Runtime.MkOrdo # r) =
                               ofPath Runtime.OS.osChangeDirectory path Runtime.MkOrdo in MkIORes r
                                 w

%cg native flat System.Foreign.System.Directory.prim__createDir
||| `createDir`: a directory made at the path; 0 when it is, -1 when it is
||| not, as the C library's `mkdir` answers, the reason the last failure.
export covering
prim__createDir : Flat.Uniform String -> PrimIO Int
prim__createDir path w = let (Runtime.MkOrdo # r) =
                               ofPath Runtime.OS.osCreateDirectory path Runtime.MkOrdo in MkIORes r
                                 w

%cg native flat System.Foreign.System.Directory.prim__removeDir
||| `removeDir`: the empty directory at the path removed, if it can be, the
||| reason the last failure if not.
export covering
prim__removeDir : Flat.Uniform String -> PrimIO ()
prim__removeDir path w = let (Runtime.MkOrdo # _) =
                               ofPath Runtime.OS.osRemoveDirectory path Runtime.MkOrdo in MkIORes ()
                                 w

%cg native flat System.Foreign.System.Directory.prim__currentDir
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
    currentOp = Runtime.Alloc.Block.allocate pathBytes Support.Ptr.nullPtr (\b => do
      let Runtime.Alloc.Block.MkAddressed p b' = Runtime.Alloc.Block.address b
      ok <- Runtime.OS.osCurrentDirectory p pathBytes
      case ok == 1 of
        True => do
          s <- Support.Text.zeroEndedText p
          Runtime.Alloc.Block.free b'
          Support.Ptr.stringPtr s
        False => do
          Runtime.Alloc.Block.free b'
          Support.Ptr.nullPtr)
