||| Files as the system tier keeps them (`File`): a mutable record
||| (`Types.Struct`), its handle, what its reads found and the offsets into
||| its input buffer as raw words, and the buffer, kept in the table of open
||| files (`table`), whose slot `base` holds the number of, a handle
||| (`Types.Represents.Handles`), as a `FilePtr`.
|||
||| Output is not buffered: each write goes to the system as it is made,
||| so that nothing waits to be flushed, and the standard output's writes,
||| by `putStr` or by its file, come out in the order they are made. Input
||| is read a buffer at a time, `bufferBytes`, the buffer made on the
||| file's first read and an empty one until then; a read takes bytes from
||| it, and asks the system again only when they run out. A line or a run
||| of bytes longer than the buffer holds grows it. The end of the file,
||| once a read finds it, is kept: the file reads nothing more, as the C
||| library's do since glibc 2.28.
|||
||| A file is rewritten in place as it is read and written. A handle is its
||| slot and the times the slot has been taken, so that a handle kept after
||| its file is closed finds none, and a use of it fails as of a bad
||| handle, never as of the file a later open put in its slot. The standard
||| files are slots 0, 1 and 2, there from the start.
module Native.System.File

import Native.System.Call

import Data.Buffer
import Data.IOArray
import Data.IORef
import Native.Failure
import Native.Flat.Uniform as Flat
import Native.Runtime.OS
import Native.Support.StructObj
import Native.Types.Struct as Types

%default total

||| A file the system tier opened. Its raw words: its handle, the system's;
||| its flags (`atEnd`, `failed`); the offsets in its buffer of the first
||| byte not yet read from it and after the last byte read into it. Its one
||| value: the buffer. Its layout is the module's own: others reach a file
||| by its operations.
export
File : Type
File = Types.Struct 4 [Buffer]

||| The flags of a file: a read found its end; a read or a write failed.
atEnd, failed : Bits64
atEnd = 1
failed = 2

||| The file's handle.
export
handle : File -> IO Bits64
handle f = Support.StructObj.readWord 0 (Flat.MkUniform f)

||| Whether the file has the flag, and the flag set.
hasFlag : File -> (flag : Bits64) -> IO Bool
hasFlag f flag = do
  w <- Support.StructObj.readWord 1 (Flat.MkUniform f)
  pure (prim__and_Bits64 w flag /= 0)

setFlag : File -> (flag : Bits64) -> IO ()
setFlag f flag = do
  w <- Support.StructObj.readWord 1 (Flat.MkUniform f)
  Support.StructObj.writeWord 1 (Flat.MkUniform f) (prim__or_Bits64 w flag)

||| Whether a read found the file's end, and whether a read or a write
||| failed: the C library's `feof` and `ferror`; and the file marked as
||| failed.
export
foundEnd, hasFailed : File -> IO Bool
foundEnd f = hasFlag f atEnd
hasFailed f = hasFlag f failed

export
markFailed : File -> IO ()
markFailed f = setFlag f failed

||| The offsets of the first unread byte and after the last byte read in,
||| and setting them.
start, end : File -> IO Int
start f = cast <$> Support.StructObj.readWord 2 (Flat.MkUniform f)
end f = cast <$> Support.StructObj.readWord 3 (Flat.MkUniform f)

setStart, setEnd : File -> Int -> IO ()
setStart f n = Support.StructObj.writeWord 2 (Flat.MkUniform f) (cast n)
setEnd f n = Support.StructObj.writeWord 3 (Flat.MkUniform f) (cast n)

||| The file's input buffer.
input : File -> IO Buffer
input f = (.value) <$> Support.StructObj.readValue 0 (Flat.MkUniform f)

||| A slot of the table: the times it has been taken, and its file while
||| it is open.
record Slot where
  constructor MkSlot
  taken : Int
  file : Maybe File

||| The slots a handle's number tells apart: the slot is the number modulo
||| this, the times it was taken the rest.
slotSpan : Int
slotSpan = 16777216

||| A new file of the system's handle, with nothing read yet.
export covering
newFile : (handle : Bits64) -> IO File
newFile h = do
  b <- emptyBuffer
  s <- Support.StructObj.new 4 1
  s <- Support.StructObj.put 0 s (Flat.MkUniform b)
  f <- Support.StructObj.done s
  Support.StructObj.writeWord 0 f h
  pure f.value

||| The table of open files, made on its first use with the standard files
||| in slots 0, 1 and 2; slots grown as files are opened.
covering
table : IORef (IOArray Slot)
-- lint: allow trust-escape: the table is made once, on its first use, as
-- the code generator keeps a constant, and each use finds it
table = unsafePerformIO $ do
  a <- newArray 16
  traverse_ (\h => do f <- newFile (cast h); ignore (writeArray a h (MkSlot 0 (Just f))))
    [0, 1, 2]
  newIORef a

||| The pointer of a standard file's slot.
export
standard : (slot : Int) -> AnyPtr
standard n = (Call.handlePointer n).value

||| The slot and the file of a pointer `base` gives back; none for a pointer
||| that is no handle, or the handle of a file closed since.
export covering
pointerFile : AnyPtr -> IO (Maybe (Int, File))
pointerFile p =
  let n = Call.pointerHandle (Flat.MkUniform p)
      slot = n `mod` slotSpan in
  if n < 0 then pure Nothing else do
    a <- readIORef table
    Just s <- readArray a slot
      | Nothing => pure Nothing
    pure (if s.taken == n `div` slotSpan then map (slot,) s.file else Nothing)

||| A new file put in a free slot of the table, grown if none is free: the
||| pointer of its handle.
export covering
register : File -> IO AnyPtr
register f = do
  a <- readIORef table
  free <- findFree a 3
  case free of
    Just (slot, taken) => do
      ignore (writeArray a slot (MkSlot (taken + 1) (Just f)))
      pure (Call.handlePointer ((taken + 1) * slotSpan + slot)).value
    Nothing => do
      a' <- newArray (2 * Data.IOArray.max a)
      traverse_ (\i => do Just s <- readArray a i
                            | Nothing => pure ()
                          ignore (writeArray a' i s))
        [0 .. Data.IOArray.max a - 1]
      writeIORef table a'
      register f
  where
    -- the first slot from `i` with no file, and the times it was taken
    covering
    findFree : IOArray Slot -> Int -> IO (Maybe (Int, Int))
    findFree a i = if i >= Data.IOArray.max a then pure Nothing else do
      s <- readArray a i
      case s of
        Nothing => pure (Just (i, 0))
        Just (MkSlot taken Nothing) => pure (Just (i, taken))
        Just _ => findFree a (i + 1)

||| A file's slot freed: its handle finds no file from now on.
export covering
release : (slot : Int) -> IO ()
release slot = do
  a <- readIORef table
  Just s <- readArray a slot
    | Nothing => pure ()
  ignore (writeArray a slot ({ file := Nothing } s))

||| More bytes read into the file's buffer, after its unread ones, which
||| move to its start: whether any came. None come once a read found the
||| end, or when a read fails, which marks the file so.
covering
more : File -> IO Bool
more f = if !(foundEnd f) then pure False else do
  room f
  b <- input f
  cap <- rawSize b
  e <- end f
  h <- handle f
  r <- Call.readInto h (Flat.MkUniform b) e (cap - e)
  if r == Runtime.OS.failedWord then do setFlag f failed; pure False
    else if r == 0 then do setFlag f atEnd; pure False
    else do setEnd f (e + cast r); pure True
  where
    ||| Room in the file's buffer after its unread bytes, which move to its
    ||| start: the buffer made on the first read, and made twice as large when
    ||| the unread bytes fill it.
    covering
    room : File -> IO ()
    room f = do
      b <- input f
      cap <- rawSize b
      s <- start f
      e <- end f
      let unread = e - s
      if cap == 0 then fresh b s unread bufferBytes
        else if unread == cap then fresh b s unread (2 * cap)
        else if s == 0 then pure ()
        else do
          copyData b s unread b 0
          setStart f 0
          setEnd f unread
      where
        ||| The bytes of a file's input buffer when it is made: 64 KiB, which few
        ||| reads of the system fill for a source file.
        bufferBytes : Int
        bufferBytes = 65536

        -- the file's input buffer replaced by another
        setInput : File -> Buffer -> IO ()
        setInput f b = Support.StructObj.writeValue 0 (Flat.MkUniform f) (Flat.MkUniform b)

        -- a new buffer of `n` bytes, the unread bytes of the old one at its start
        covering
        fresh : Buffer -> (s, unread, n : Int) -> IO ()
        fresh old s unread n = do
          Just b <- newBuffer n
            | Nothing => pure ()
          copyData old s unread b 0
          setInput f b
          setStart f 0
          setEnd f unread

||| The file's next `n` unread bytes as a string, which are read then.
covering
takeBytes : File -> (n : Int) -> IO String
takeBytes f n = do
  b <- input f
  s <- start f
  setStart f (s + n)
  getString b s n

||| The file's text through the next newline, or to its end, or to a read
||| that fails: the C library's `getline`.
export covering
readLine : File -> IO String
readLine f = from 0
  where
    -- the line's bytes searched from `i` past the file's first unread byte
    covering
    from : Int -> IO String
    from i = do
      s <- start f
      e <- end f
      b <- input f
      nl <- Call.newlineFrom (Flat.MkUniform b) (s + i) e
      if nl < e then takeBytes f (nl + 1 - s) else do
        got <- more f
        if got then from (e - s) else do
          s' <- start f
          e' <- end f
          takeBytes f (e' - s')

||| At most `n` bytes of the file's text, as many as there are before its
||| end or a read that fails: the C library's `fread`.
export covering
readChars : File -> (n : Int) -> IO String
readChars f n = do
  s <- start f
  e <- end f
  if e - s >= n then takeBytes f n else do
    got <- more f
    if got then readChars f n else do
      s' <- start f
      e' <- end f
      takeBytes f (e' - s')

||| The file's next byte, or -1 at its end or for a read that fails: the C
||| library's `fgetc`.
export covering
readByte : File -> IO Int
readByte f = do
  s <- start f
  e <- end f
  if s < e
    then do
      b <- input f
      c <- getBits8 b s
      setStart f (s + 1)
      pure (cast c)
    else do
      got <- more f
      if got then readByte f else pure (-1)

||| The file's bytes through the next newline, or to its end, passed over;
||| whether no read failed: the C support's `seekLine`.
export covering
skipLine : File -> IO Bool
skipLine f = do
  s <- start f
  e <- end f
  b <- input f
  nl <- Call.newlineFrom (Flat.MkUniform b) s e
  if nl < e then do setStart f (nl + 1); pure True else do
    setStart f e
    got <- more f
    if got then skipLine f else map not (hasFailed f)

||| At most `n` of the file's bytes read into the buffer from the offset, as
||| many as there are before its end or a read that fails: those in its
||| buffer first, the rest read from the system straight there, so that a
||| large read passes through no other buffer; how many.
export covering
readInto : File -> Buffer -> (offset, n : Int) -> IO Int
readInto f dst offset n = do
  s <- start f
  e <- end f
  b <- input f
  let k = min (e - s) n
  copyData b s k dst offset
  setStart f (s + k)
  direct k
  where
    -- the bytes from `i` read from the system, until `n`, the end or a
    -- read that fails
    covering
    direct : Int -> IO Int
    direct i = if i >= n || !(foundEnd f) then pure i else do
      h <- handle f
      r <- Call.readInto h (Flat.MkUniform dst) (offset + i) (n - i)
      if r == Runtime.OS.failedWord then do setFlag f failed; pure i
        else if r == 0 then do setFlag f atEnd; pure i
        else direct (i + cast r)

||| `use` of the file of a pointer `base` gives back and its slot; `none`,
||| with the last failure that the handle is bad, for a pointer that is no
||| handle, or the handle of a file closed since.
export covering
withFile : AnyPtr -> (none : a) -> (use : Int -> File -> IO a) -> IO a
withFile p none use = do
  Just (slot, f) <- pointerFile p
    | Nothing => do
        Call.recordFailure (Failure.code Failure.BadHandle)
        pure none
  use slot f
