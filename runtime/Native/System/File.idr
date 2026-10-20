||| Files as the system tier keeps them (`File`): a value of an ordinary
||| record, its handle, what its reads found, and its input buffer, kept in
||| the table of open files (`table`), whose slot `base` holds the number
||| of, a handle (`Types.Represents.Handles`), as a `FilePtr`.
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
||| A file is a value, not mutated: an operation reads it from its slot and
||| writes the file it makes back, its buffer's bytes the one thing written
||| in place. A handle is its slot and the times the slot has been taken,
||| so that a handle kept after its file is closed finds none, and a use of
||| it fails as of a bad handle, never as of the file a later open put in
||| its slot. The standard files are slots 0, 1 and 2, there from the
||| start.
module Native.System.File

import Native.System.Call

import Data.Buffer
import Data.IOArray
import Data.IORef
import Native.Failure
import Native.Flat.Uniform as Flat
import Native.Runtime.OS

%default total

||| A file the system tier opened: its handle, the system's; whether a read
||| found its end, and whether a read or a write failed; the offsets in its
||| buffer of the first byte not yet read from it and after the last byte
||| read into it; and the buffer.
public export
record File where
  constructor MkFile
  handle : Bits64
  atEnd, failed : Bool
  start, end : Int
  input : Buffer

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
export
newFile : (handle : Bits64) -> IO File
newFile h = do
  b <- emptyBuffer
  pure (MkFile h False False 0 0 b)

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
fileOf : AnyPtr -> IO (Maybe (Int, File))
fileOf p =
  let n = Call.pointerHandle (MkUniform p)
      slot = n `mod` slotSpan in
  if n < 0 then pure Nothing else do
    a <- readIORef table
    Just s <- readArray a slot
      | Nothing => pure Nothing
    pure (if s.taken == n `div` slotSpan then map (slot,) s.file else Nothing)

||| The file of a slot written back.
export covering
keep : (slot : Int) -> File -> IO ()
keep slot f = do
  a <- readIORef table
  Just s <- readArray a slot
    | Nothing => pure ()
  ignore (writeArray a slot ({ file := Just f } s))

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

||| The file with more bytes read into its buffer, after its unread ones,
||| which move to its start, and whether any came. None come once a read
||| found the end, or when a read fails, which marks the file so.
covering
more : File -> IO (File, Bool)
more f =
  if f.atEnd then pure (f, False) else do
    f' <- room f
    cap <- rawSize f'.input
    r <- Call.readInto f'.handle (MkUniform f'.input) f'.end (cap - f'.end)
    pure (if r == Runtime.OS.failedWord then ({ failed := True } f', False)
          else if r == 0 then ({ atEnd := True } f', False)
          else ({ end := f'.end + cast r } f', True))
  where
    ||| Room in the file's buffer after its unread bytes, which move to its
    ||| start: the buffer made on the first read, and made twice as large when
    ||| the unread bytes fill it.
    covering
    room : File -> IO File
    room f = do
      cap <- rawSize f.input
      let unread = f.end - f.start
      if cap == 0 then fresh bufferBytes unread
        else if unread == cap then fresh (2 * cap) unread
        else if f.start == 0 then pure f
        else do
          copyData f.input f.start unread f.input 0
          pure ({ start := 0, end := unread } f)
      where
        -- a new buffer of `n` bytes, the unread bytes of the old one at its start
        covering
        fresh : Int -> (unread : Int) -> IO File
        fresh n unread = do
          Just b <- newBuffer n
            | Nothing => pure f
          copyData f.input f.start unread b 0
          pure ({ input := b, start := 0, end := unread } f)

        ||| The bytes of a file's input buffer when it is made: 64 KiB, which few
        ||| reads of the system fill for a source file.
        bufferBytes : Int
        bufferBytes = 65536

||| The file's next `n` unread bytes as a string, which are read then.
covering
takeBytes : File -> (n : Int) -> IO (File, String)
takeBytes f n = do
  s <- getString f.input f.start n
  pure ({ start := f.start + n } f, s)

||| The file's text through the next newline, or to its end, or to a read
||| that fails: the C library's `getline`.
export covering
readLine : File -> IO (File, String)
readLine f = from f 0
  where
    -- the line's bytes searched from `i` past the file's first unread byte
    covering
    from : File -> Int -> IO (File, String)
    from f i = do
      nl <- Call.newlineFrom (MkUniform f.input) (f.start + i) f.end
      if nl < f.end then takeBytes f (nl + 1 - f.start) else do
        (f', got) <- more f
        if got then from f' (f.end - f.start) else takeBytes f' (f'.end - f'.start)

||| At most `n` bytes of the file's text, as many as there are before its
||| end or a read that fails: the C library's `fread`.
export covering
readChars : File -> (n : Int) -> IO (File, String)
readChars f n =
  if f.end - f.start >= n then takeBytes f n else do
    (f', got) <- more f
    if got then readChars f' n else takeBytes f' (f'.end - f'.start)

||| The file's next byte, or -1 at its end or for a read that fails: the C
||| library's `fgetc`.
export covering
readByte : File -> IO (File, Int)
readByte f =
  if f.start < f.end then do
      b <- getBits8 f.input f.start
      pure ({ start := f.start + 1 } f, cast b)
    else do
      (f', got) <- more f
      if got then readByte f' else pure (f', -1)

||| The file's bytes through the next newline, or to its end, passed over;
||| whether no read failed: the C support's `seekLine`.
export covering
skipLine : File -> IO (File, Bool)
skipLine f = do
  nl <- Call.newlineFrom (MkUniform f.input) f.start f.end
  if nl < f.end then pure ({ start := nl + 1 } f, True) else do
    (f', got) <- more ({ start := f.end } f)
    if got then skipLine f' else pure (f', not f'.failed)

||| At most `n` of the file's bytes read into the buffer from the offset, as
||| many as there are before its end or a read that fails: those in its
||| buffer first, the rest read from the system straight there, so that a
||| large read passes through no other buffer; how many.
export covering
readInto : File -> Buffer -> (offset, n : Int) -> IO (File, Int)
readInto f b offset n = do
  let k = min (f.end - f.start) n
  copyData f.input f.start k b offset
  direct ({ start := f.start + k } f) k
  where
    -- the bytes from `i` read from the system, until `n`, the end or a
    -- read that fails
    covering
    direct : File -> Int -> IO (File, Int)
    direct f i = if i >= n || f.atEnd then pure (f, i) else do
      r <- Call.readInto f.handle (MkUniform b) (offset + i) (n - i)
      if r == Runtime.OS.failedWord then pure ({ failed := True } f, i)
        else if r == 0 then pure ({ atEnd := True } f, i)
        else direct f (i + cast r)

||| `use` of the file of a pointer `base` gives back and its slot; `none`,
||| with the last failure that the handle is bad, for a pointer that is no
||| handle, or the handle of a file closed since.
export covering
withFile : AnyPtr -> (none : a) -> (use : Int -> File -> IO a) -> IO a
withFile p none use = do
  Just (slot, f) <- fileOf p
    | Nothing => do
        Call.recordFailure (Failure.code Failure.BadHandle)
        pure none
  use slot f
