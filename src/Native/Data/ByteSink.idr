||| A stretch of a buffer that bytes are written into (`ByteSink`), from its
||| first byte to its last, the writes checked against the stretch's end:
||| what writes a large run of bytes, such as an image's text or its
||| read-only data, one piece at a time, with no list of its bytes made
||| first.
|||
||| A sink is opened only over a stretch that lies inside its buffer, and a
||| write that would pass the stretch's end writes nothing and gives no
||| sink, so no write through one lands outside its stretch: a buffer's own
||| writes check no bounds where Idris's Chez code is compiled unsafe. A
||| piece of several parts, such as an instruction, is written with one
||| check (`fits`), through a span over the bytes it takes (`Span`), whose
||| type says how many are left: each part's write takes its width from
||| them, so the typechecker sees that the parts take the piece's bytes.
|||
||| A number of 4 or 8 bytes is written low byte first, as every target in
||| scope orders its bytes (`Native.Data.LittleEndian`), by one write of
||| the buffer's. `Data.Buffer` writes a number low byte first under this
||| code generator (`Native.Support.BufferObj`), RefC and JavaScript; under
||| Chez, which compiles this code, in the order of the host it runs on
||| (`native-endianness`), and the host is assumed little-endian, as every
||| platform in scope is.
module Native.Data.ByteSink

import Native.Data.Inside

import Data.Buffer

%default total

||| The part of a stretch still to write: its buffer, the next byte's
||| offset and the stretch's end, one past its last byte. Abstract: made by
||| `sink` alone.
export
record ByteSink where
  constructor MkByteSink
  buffer : Buffer
  next : Int
  end : Int

||| A sink over the `size` bytes of the buffer from `at`, if they lie inside
||| it (`isInside`).
export
sink : Buffer -> (at, size : Int) -> IO (Maybe ByteSink)
sink buf at size = do
  n <- rawSize buf
  pure (if Inside.isInside n at size then Just (MkByteSink buf at (at + size))
          else Nothing)

||| Whether the stretch is written to its end.
export
full : ByteSink -> Bool
full s = s.next == s.end

------------------------------------------------------------------------------
-- Spans

||| The next `n` bytes of the sink `s`, to be written in order: each write
||| below takes its width from the front of the bytes left, which the type
||| says. A span of no bytes is a place in the stretch, where the next
||| bytes are written from: the sink's next offset (`start`), or the end
||| of the bytes a span was written to. At run time a span is the offset
||| of its next byte, and makes no object of its own. Abstract: made by
||| `start` and `span` alone, over bytes that fit before the sink's end, so
||| that no write through a span passes it, with no check of its own.
export
data Span : ByteSink -> Nat -> Type where
  MkSpan : (next : Int) -> Span s n

||| The place of the sink's next offset.
export
start : (s : ByteSink) -> Span s 0
start s = MkSpan s.next

||| Whether the `n` bytes from a place fit before the sink's end: the one
||| check of every write. The count is compared with the bytes left as a
||| `Nat`, before it is made an `Int`, which one past the largest `Int`
||| would wrap to a count that fits or one below 0.
export
fits : (s : ByteSink) -> (at : Span s 0) -> (n : Nat) -> Bool
fits s (MkSpan i) n = n <= cast (s.end - i)

||| A span over the `n` bytes from a place, which fit before the sink's end
||| (`fits`).
export
span : (s : ByteSink) -> (at : Span s 0) -> (0 n : Nat) -> (0 _ : fits s at n = True) -> Span s n
span s (MkSpan i) _ _ = MkSpan i

||| What is left of the sink from a place.
export
past : (s : ByteSink) -> Span s 0 -> ByteSink
past s (MkSpan i) = { next := i } s

||| A byte written at the span's next byte.
export
putBits8 : (s : ByteSink) -> Span s (S n) -> Bits8 -> IO (Span s n)
putBits8 s (MkSpan i) b = do setBits8 s.buffer i b; pure (MkSpan (i + 1))

||| A number's four bytes written at the span's next byte, low byte first.
export
putBits32 : (s : ByteSink) -> Span s (4 + n) -> Bits32 -> IO (Span s n)
putBits32 s (MkSpan i) v = do setBits32 s.buffer i v; pure (MkSpan (i + 4))

||| A number's eight bytes written at the span's next byte, low byte first.
export
putBits64 : (s : ByteSink) -> Span s (8 + n) -> Bits64 -> IO (Span s n)
putBits64 s (MkSpan i) v = do setBits64 s.buffer i v; pure (MkSpan (i + 8))

||| The bytes written at the span's next byte.
export
putBytes : (s : ByteSink) -> (bs : List Bits8) -> Span s (length bs + n) -> IO (Span s n)
putBytes s bs sp = fromPrim (go bs sp)
  where
    -- the world passed by hand: an `IO` loop that ends in a call of
    -- itself, Idris compiles as one that makes an action at each byte
    go : (bs : List Bits8) -> Span s (length bs + n) -> PrimIO (Span s n)
    go [] sp w = MkIORes sp w
    go (b :: rest) sp w = case toPrim (putBits8 s sp b) w of
      MkIORes sp' w' => go rest sp' w'

||| The `k` bytes of `src` from `from` copied at the span's next byte, by one
||| copy of the buffer's, if they lie inside `src` (`isInside`): the span
||| past them, or none, with nothing written. The count made an `Int` does
||| not wrap: the span holds its bytes, and a span is made only over bytes
||| that fit before the sink's end (`fits`).
export
putBuffer : (s : ByteSink) -> (src : Buffer) -> (from : Int) -> (k : Nat) -> Span s (k + n) ->
            IO (Maybe (Span s n))
putBuffer s src from k (MkSpan i) = do
  m <- rawSize src
  if Inside.isInside m from (cast k)
    then do copyData src from (cast k) s.buffer i; pure (Just (MkSpan (i + cast k)))
    else pure Nothing

||| `k` copies of the byte written at the span's next byte.
export
putCopies : (s : ByteSink) -> (k : Nat) -> Bits8 -> Span s (k + n) -> IO (Span s n)
putCopies s k b sp = fromPrim (go k sp)
  where
    -- the world passed by hand: in an `IO` loop, the match on `S` binds
    -- the count's predecessor before the write, and Idris compiles the
    -- loop as one that makes an action at each byte
    go : (k : Nat) -> Span s (k + n) -> PrimIO (Span s n)
    go Z sp w = MkIORes sp w
    go (S k) sp w = case toPrim (putBits8 s sp b) w of
      MkIORes sp' w' => go k sp' w'

------------------------------------------------------------------------------
-- Pieces of one part

||| The bytes written at the next offset, if they fit before the end.
export
put : ByteSink -> List Bits8 -> IO (Maybe ByteSink)
put s bs with (fits s (start s) (length bs + 0)) proof ok
  _ | True = do end <- putBytes s bs (span s (start s) _ ok); pure (Just (past s end))
  _ | False = pure Nothing

||| `n` zero bytes written at the next offset, if they fit before the end.
export
zeros : ByteSink -> Nat -> IO (Maybe ByteSink)
zeros s n with (fits s (start s) (n + 0)) proof ok
  _ | True = do end <- putCopies s n 0 (span s (start s) _ ok); pure (Just (past s end))
  _ | False = pure Nothing
