||| The foreign functions of `base`'s `System.File.ReadWrite`, as the system
||| tier implements them: a file's lines, bytes and end read, strings
||| written to it (`Native.System.File`), and files removed, each an
||| ordinary function of the foreign one's name and type (`Native.System`
||| says how they are bound).
module Native.System.Foreign.System.File.ReadWrite

import Native.Flat.Uniform as Flat
import Native.System.Call
import Native.System.File

%default total

||| `fSeekLine`: the file's bytes through the next newline, or to its end,
||| passed over; 0, or -1 if a read failed.
export covering
prim__seekLine : AnyPtr -> PrimIO Int
prim__seekLine p = toPrim $ File.withFile p (-1) (\_, f => do
  ok <- File.skipLine f
  pure (if ok then 0 else -1))

||| `fGetLine`: the file's text through the next newline, the newline
||| kept, or to its end, the empty string there, as a string given as the
||| pointer (`Support.Ptr`), which `base` reads at once.
export covering
prim__readLine : AnyPtr -> PrimIO (Ptr String)
prim__readLine p = toPrim $ File.withFile p Call.nullString.value (\_, f => do
  s <- File.readLine f
  pure (Call.stringPointer (MkUniform s)).value)

||| `fGetChars`: at most `n` bytes of the file's text, as many as there are
||| before its end or a read that fails, as a string given as the pointer;
||| the null pointer if there are none, which `base` reads as the empty
||| string, or the failure the file's.
export covering
prim__readChars : Int -> AnyPtr -> PrimIO (Ptr String)
prim__readChars n p = toPrim $
  if n <= 0 then pure Call.nullString.value else
    File.withFile p Call.nullString.value (\_, f => do
      s <- File.readChars f n
      pure (if s == "" then Call.nullString.value else (Call.stringPointer (MkUniform s)).value))

||| `fGetChar`: the file's next byte, or -1 at its end or for a read that
||| fails, as the C library's `fgetc`.
export covering
prim__readChar : AnyPtr -> PrimIO Int
prim__readChar p = toPrim $ File.withFile p (-1) (\_, f => File.readByte f)

||| `fPutStr`: the string's text written to the file, all of it; 1 if it
||| was, 0 if not, the file then marked as failed.
export covering
prim__writeLine : AnyPtr -> String -> PrimIO Int
prim__writeLine p s = toPrim $ File.withFile p 0 (\_, f => do
  ok <- Call.writeText !(File.handle f) (MkUniform s)
  if ok then pure 1 else do
    File.markFailed f
    pure 0)

||| `fEOF`: 1 once a read found the file's end, 0 before; 1 for a closed
||| file, which reads nothing more.
export covering
prim__eof : AnyPtr -> PrimIO Int
prim__eof p = toPrim $ File.withFile p 1 (\_, f => do
  e <- File.foundEnd f
  pure (if e then 1 else 0))

||| `removeFile`: the file at the path removed, or the empty directory, as
||| the C library's `remove`; 0 if it is, -1 if not, the reason the last
||| failure.
export covering
prim__removeFile : String -> PrimIO Int
prim__removeFile path = toPrim $ do
  ok <- Call.removePath (MkUniform path)
  pure (if ok then 0 else -1)
