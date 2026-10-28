||| A stretch of a buffer that bytes are written into, from its first byte
||| to its last, each write checked against the stretch's end: what writes
||| an image's text or its read-only data into the image, one piece at a
||| time, with no list of the stretch's bytes made first.
|||
||| A sink is opened only over a stretch that lies inside its buffer, and a
||| write that would pass the stretch's end writes nothing and gives no
||| sink, so no write through one lands outside its stretch: a buffer's own
||| writes check no bounds where Idris's Chez code is compiled unsafe.
|||
||| A number of 4 or 8 bytes is written low byte first, as every target in
||| scope orders its bytes (`Native.Codegen.LittleEndian`), by one write of
||| the buffer's. `Data.Buffer` writes a number low byte first under this
||| code generator (`Native.Support.BufferObj`), RefC and JavaScript; under
||| Chez, which compiles this code, in the order of the host it runs on
||| (`native-endianness`), and the host is assumed little-endian, as every
||| platform in scope is.
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
  -- the size compared with the bytes left past `at`: `at + size` could
  -- wrap past the largest `Int`
  pure (if 0 <= at && 0 <= size && at <= n && size <= n - at then Just (MkSink buf at (at + size))
          else Nothing)

||| Whether the stretch is written to its end.
export
full : Sink -> Bool
full s = s.next == s.end

||| The sink past the next `n` bytes, if they fit before the end: the one
||| check of every write, of a count `n` that is never negative.
advance : Sink -> (n : Int) -> Maybe Sink
advance s n = let next = s.next + n in if next <= s.end then Just ({ next := next } s) else Nothing

-- Each write below is a `case` of `advance`'s answer whose every branch is
-- an action: Idris then compiles the write as a function of its arguments
-- and the world, which a `let` around the branches would make a function
-- that makes an action, at each write.

||| The bytes written at the next offset, if they fit before the end.
export
put : Sink -> List Bits8 -> IO (Maybe Sink)
put s bs = case advance s (cast (length bs)) of
  Nothing => pure Nothing
  past@(Just _) => do go s.next bs; pure past
  where
    go : Int -> List Bits8 -> IO ()
    go _ [] = pure ()
    go i (b :: rest) = do setBits8 s.buffer i b; go (i + 1) rest

||| A byte written at the next offset, if it fits before the end.
export
putBits8 : Sink -> Bits8 -> IO (Maybe Sink)
putBits8 s b = case advance s 1 of
  Nothing => pure Nothing
  past@(Just _) => do setBits8 s.buffer s.next b; pure past

||| A number's four bytes written at the next offset, low byte first, if
||| they fit before the end.
export
putBits32 : Sink -> Bits32 -> IO (Maybe Sink)
putBits32 s v = case advance s 4 of
  Nothing => pure Nothing
  past@(Just _) => do setBits32 s.buffer s.next v; pure past

||| A number's eight bytes written at the next offset, low byte first, if
||| they fit before the end.
export
putBits64 : Sink -> Bits64 -> IO (Maybe Sink)
putBits64 s v = case advance s 8 of
  Nothing => pure Nothing
  past@(Just _) => do setBits64 s.buffer s.next v; pure past

||| `n` zero bytes written at the next offset, if they fit before the end.
export
zeros : Sink -> Nat -> IO (Maybe Sink)
-- the count compared with the bytes left as a `Nat`, before it is made an
-- `Int`: one past the largest `Int` would wrap, to a count that fits or one
-- below 0
zeros s n = case (if cast (s.end - s.next) < n then Nothing else advance s (cast n)) of
  Nothing => pure Nothing
  past@(Just _) => do fromPrim (go s.next n); pure past
  where
    -- `k` zeros from offset `i`, the world passed by hand: in an `IO`
    -- loop, the match on `S` binds the count's predecessor before the
    -- write, and Idris compiles the loop as one that makes an action at
    -- each byte
    go : (i : Int) -> (k : Nat) -> PrimIO ()
    go _ Z w = MkIORes () w
    go i (S k) w = case toPrim (setBits8 s.buffer i 0) w of
      MkIORes () w' => go (i + 1) k w'
