||| A buffer that grows as it fills (`GrowingBuffer`): its bytes, of which
||| the first are filled, the rest room to fill. When more room is wanted
||| than it has, it is copied into one twice its size, or of the size
||| wanted if that is more (`grownTo`), the one rule of every growing table
||| of the code generator, so that filling n bytes copies fewer than 2n.
|||
||| Every read and write is checked against the buffer's size, so that
||| none lands outside it where Idris's Chez code is compiled unsafe: a
||| write past it writes nothing, and a read past it reads 0. A new buffer
||| is all zeros, under every code generator (Chez, RefC, JavaScript and
||| this one), and so is the room a buffer grows by, which a table that
||| reads 0 for a cell not yet written relies on. Bytes written through a
||| sink over the room (`sink`) count as filled once `filledTo` says so.
module Native.Data.GrowingBuffer

import Native.Data.ByteSink

import Data.Buffer

%default total

||| A buffer of `capacity` bytes, the first `used` filled. Abstract: made by
||| `growingBuffer` and `grownTo` alone, so that `capacity` is the
||| buffer's size and `used` lies between 0 and it.
export
record GrowingBuffer where
  constructor MkGrowingBuffer
  buffer : Buffer
  capacity : Int
  used : Int

||| A buffer of `capacity` bytes to begin with, all zeros, none filled; of
||| none, if one that large cannot be made.
export
growingBuffer : (capacity : Int) -> IO GrowingBuffer
growingBuffer n = do
  b <- newBuffer n >>= maybe emptyBuffer pure
  m <- rawSize b
  pure (MkGrowingBuffer b m 0)

||| The bytes it holds, filled or not.
export
capacity : GrowingBuffer -> Int
capacity g = g.capacity

||| The bytes filled.
export
used : GrowingBuffer -> Int
used g = g.used

||| The buffer with at least `bytes` bytes: this one, if it has them; else
||| a copy of it into one of twice its bytes, or of `bytes` if that is
||| more, every byte it has kept, written through a sink or not, and as
||| many filled, the rest zeros; none if no buffer that large can be made.
export
grownTo : GrowingBuffer -> (bytes : Int) -> IO (Maybe GrowingBuffer)
grownTo g n =
  if n <= g.capacity then pure (Just g) else grown (max (2 * g.capacity) n)
  where
    grown : Int -> IO (Maybe GrowingBuffer)
    grown size = do
      Just b <- resizeBuffer g.buffer size
        | Nothing => pure Nothing
      m <- rawSize b
      pure (if m < n then Nothing else Just (MkGrowingBuffer b m g.used))

||| The buffer with room for `more` bytes past those filled (`grownTo`).
export
grownFor : GrowingBuffer -> (more : Int) -> IO (Maybe GrowingBuffer)
grownFor g more = grownTo g (g.used + more)

||| The buffer with its first `used` bytes filled, as many as it holds if
||| `used` is more, none if it is below 0.
export
filledTo : GrowingBuffer -> (used : Int) -> GrowingBuffer
filledTo g n = { used := max 0 (min n g.capacity) } g

||| Whether the `width` bytes from `at` lie in the buffer.
within : GrowingBuffer -> (at, width : Int) -> Bool
within g at width = 0 <= at && at <= g.capacity - width

||| The byte at `at`; 0 past the buffer.
export
getBits8 : GrowingBuffer -> (at : Int) -> IO Bits8
getBits8 g at = if within g at 1 then Data.Buffer.getBits8 g.buffer at else pure 0

||| The word at `at`, as an `Int`, low byte first; 0 past the buffer.
export
getInt : GrowingBuffer -> (at : Int) -> IO Int
getInt g at = if within g at 8 then Data.Buffer.getInt g.buffer at else pure 0

||| The byte written at `at`, if it lies in the buffer.
export
setBits8 : GrowingBuffer -> (at : Int) -> Bits8 -> IO ()
setBits8 g at v = if within g at 1 then Data.Buffer.setBits8 g.buffer at v else pure ()

||| The number's four bytes written at `at`, low byte first, if they lie in
||| the buffer.
export
setBits32 : GrowingBuffer -> (at : Int) -> Bits32 -> IO ()
setBits32 g at v = if within g at 4 then Data.Buffer.setBits32 g.buffer at v else pure ()

||| The word written at `at`, low byte first, if it lies in the buffer.
export
setInt : GrowingBuffer -> (at : Int) -> Int -> IO ()
setInt g at v = if within g at 8 then Data.Buffer.setInt g.buffer at v else pure ()

||| A sink over the room past the filled bytes.
export
sink : GrowingBuffer -> IO (Maybe ByteSink)
sink g = ByteSink.sink g.buffer g.used (g.capacity - g.used)

||| The filled bytes written at the sink's next offset, with one copy, if
||| they fit before its end.
export
put : ByteSink -> GrowingBuffer -> IO (Maybe ByteSink)
put s g = copied (cast g.used) (ByteSink.fits s (ByteSink.start s) (cast g.used + 0)) Refl
  where
    copied : (k : Nat) -> (fit : Bool) -> (0 _ : ByteSink.fits s (ByteSink.start s) (k + 0) = fit) ->
             IO (Maybe ByteSink)
    copied k False _ = pure Nothing
    copied k True fit = do
      Just end <- ByteSink.putBuffer s g.buffer 0 k (ByteSink.span s (ByteSink.start s) (k + 0) fit)
        | Nothing => pure Nothing
      pure (Just (ByteSink.past s end))
