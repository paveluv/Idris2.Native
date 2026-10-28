||| A stretch of a buffer that bytes are written into, from its first byte
||| to its last, each write checked against the stretch's end: what writes
||| an image's text or its read-only data into the image, one piece at a
||| time, with no list of the stretch's bytes made first.
|||
||| A sink is opened only over a stretch that lies inside its buffer, and a
||| write that would pass the stretch's end writes nothing and gives no
||| sink, so no write through one lands outside its stretch: a buffer's own
||| writes check no bounds where Idris's Chez code is compiled unsafe.
module Native.Codegen.ByteSink

import Data.Buffer

%default total

||| The part of a stretch still to write: its buffer, the next byte's
||| offset and the stretch's end, one past its last byte. Abstract: made by
||| `sink` alone.
export
record Sink where
  constructor MkSink
  buffer : Buffer
  next : Int
  end : Int

||| A sink over the `size` bytes of the buffer from `at`, if they lie inside
||| it.
export
sink : Buffer -> (at, size : Int) -> IO (Maybe Sink)
sink buf at size = do
  n <- rawSize buf
  pure (if 0 <= at && 0 <= size && at + size <= n then Just (MkSink buf at (at + size))
          else Nothing)

||| Whether the stretch is written to its end.
export
full : Sink -> Bool
full s = s.next == s.end

||| The bytes written at the next offset, if they fit before the end.
export
put : Sink -> List Bits8 -> IO (Maybe Sink)
put s bs =
  let n = the Int (cast (length bs))
  in if s.next + n <= s.end then do go s.next bs; pure (Just ({ next := s.next + n } s))
       else pure Nothing
  where
    go : Int -> List Bits8 -> IO ()
    go _ [] = pure ()
    go i (b :: rest) = do setBits8 s.buffer i b; go (i + 1) rest

||| `n` zero bytes written at the next offset, if they fit before the end.
export
zeros : Sink -> Nat -> IO (Maybe Sink)
zeros s n =
  let k = the Int (cast n)
  in if s.next + k <= s.end then do go s.next n; pure (Just ({ next := s.next + k } s))
       else pure Nothing
  where
    go : Int -> Nat -> IO ()
    go _ Z = pure ()
    go i (S m) = do setBits8 s.buffer i 0; go (i + 1) m
