||| The foreign functions of `base`'s `System.File.Handle`, as the system
||| tier implements them: files opened and closed (`Native.System.File`),
||| each an ordinary function of the foreign one's name and type
||| (`Native.System` says how they are bound).
module Native.System.Foreign.System.File.Handle

import Native.Failure
import Native.Flat.Uniform as Flat
import Native.OpenFlag
import Native.Runtime.OS
import Native.System.Call
import Native.System.File

%default total

||| `openFile`: the file at the path opened in the C library's mode; the
||| null pointer if it is not, the reason the last failure, `Invalid` for
||| a mode the C library does not take.
export covering
prim__open : String -> String -> PrimIO AnyPtr
prim__open path mode = toPrim $ do
  let flags = modeFlags (unpack mode)
  if flags == 0
    then do
      Call.recordFailure (Failure.code Failure.Invalid)
      pure Call.nullPointer.value
    else do
      h <- Call.openPath (MkUniform path) flags
      if h == Runtime.OS.failedWord then pure Call.nullPointer.value else do
        f <- File.newFile h
        File.register f
  where
    ||| The flags of the C library's mode: `r`, `w` or `a`, then `+`, `b` or
    ||| any letter the C library takes, in any order, of which only `+` changes
    ||| the flags; 0, no flags, for any other.
    modeFlags : List Char -> Bits64
    modeFlags [] = 0
    modeFlags (c :: rest) =
      let both = if elem '+' rest then bits [OpenFlag.ForReading, OpenFlag.ForWriting] else 0 in
      prim__or_Bits64 both
        (case c of
           'r' => bits [OpenFlag.ForReading]
           'w' => bits [OpenFlag.ForWriting, OpenFlag.Create, OpenFlag.Truncate]
           'a' => bits [OpenFlag.ForWriting, OpenFlag.Create, OpenFlag.Append]
           _ => 0)
      where
        bits : List OpenFlag -> Bits64
        bits = foldl (\w, f => prim__or_Bits64 w (OpenFlag.bit f)) 0

||| `closeFile`: the file closed, its handle finding no file from now on.
export covering
prim__close : AnyPtr -> PrimIO ()
prim__close p = toPrim $ File.withFile p () (\slot, f => do
  Call.close f.handle
  File.release slot)
