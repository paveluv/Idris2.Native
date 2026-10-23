||| The foreign functions of `base`'s `System.File.Meta`, as the system tier
||| implements them: what a file is (`Native.System.File`), each an
||| ordinary function of the foreign one's name and type (`Native.System`
||| says how they are bound).
module Native.System.Foreign.System.File.Meta

import Native.Flat.Uniform as Flat
import Native.Runtime.OS
import Native.System.Call
import Native.System.File
import Native.System.Foreign.System.FFI

%default total

||| `fileSize`: the bytes of the file; -1 if the system does not say, the
||| reason the last failure.
export covering
prim__fileSize : AnyPtr -> PrimIO Int
prim__fileSize p = toPrim $ File.withFile p (-1) (\_, f => do
  n <- Call.fileSize !(File.handle f)
  pure (if n == Runtime.OS.failedWord then -1 else cast n))

||| `fileTime`: the file's times, in a block of six words `malloc` gives,
||| as C's support makes its structure, which `base` reads by the six
||| functions below and frees (`Call.fileTimes`); its first word -1 if the
||| system does not say, the reason the last failure.
export covering
prim__fileTime : AnyPtr -> PrimIO AnyPtr
prim__fileTime p = toPrim $ File.withFile p Call.nullPointer.value (\_, f => do
  t <- primIO (FFI.prim__malloc 48)
  Call.fileTimes !(File.handle f) t
  pure t.value)

||| The times of a block `fileTime` gave: the last access's, modification's
||| and change of status's seconds and nanoseconds.
export covering
prim__filetimeAccessTimeSec, prim__filetimeAccessTimeNsec : AnyPtr -> PrimIO Int
prim__filetimeAccessTimeSec t = toPrim (Call.timesWord (Flat.MkUniform t) 0)
prim__filetimeAccessTimeNsec t = toPrim (Call.timesWord (Flat.MkUniform t) 1)

export covering
prim__filetimeModifiedTimeSec, prim__filetimeModifiedTimeNsec : AnyPtr -> PrimIO Int
prim__filetimeModifiedTimeSec t = toPrim (Call.timesWord (Flat.MkUniform t) 2)
prim__filetimeModifiedTimeNsec t = toPrim (Call.timesWord (Flat.MkUniform t) 3)

export covering
prim__filetimeStatusTimeSec, prim__filetimeStatusTimeNsec : AnyPtr -> PrimIO Int
prim__filetimeStatusTimeSec t = toPrim (Call.timesWord (Flat.MkUniform t) 4)
prim__filetimeStatusTimeNsec t = toPrim (Call.timesWord (Flat.MkUniform t) 5)

||| `isTTY`: 1 if the file is a terminal's, 0 if not.
export covering
prim__fileIsTTY : AnyPtr -> PrimIO Int
prim__fileIsTTY p = toPrim $ File.withFile p 0 (\_, f => do
  t <- Call.isTerminal !(File.handle f)
  pure (if t then 1 else 0))
