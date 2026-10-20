||| The foreign functions of `base`'s `System.File.Meta`, as the system tier
||| implements them: what a file is (`Native.System.File`), each an
||| ordinary function of the foreign one's name and type (`Native.System`
||| says how they are bound).
module Native.System.Foreign.System.File.Meta

import Native.Runtime.OS
import Native.System.Call
import Native.System.File

%default total

||| `fileSize`: the bytes of the file; -1 if the system does not say, the
||| reason the last failure.
export covering
prim__fileSize : AnyPtr -> PrimIO Int
prim__fileSize p = toPrim $ File.withFile p (-1) (\_, f => do
  n <- Call.fileSize !(File.handle f)
  pure (if n == Runtime.OS.failedWord then -1 else cast n))

||| `isTTY`: 1 if the file is a terminal's, 0 if not.
export covering
prim__fileIsTTY : AnyPtr -> PrimIO Int
prim__fileIsTTY p = toPrim $ File.withFile p 0 (\_, f => do
  t <- Call.isTerminal !(File.handle f)
  pure (if t then 1 else 0))
