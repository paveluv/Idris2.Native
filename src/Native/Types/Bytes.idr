||| Immutable bytes (`Bytes`): words made once, then only read, by a pure
||| load (`uncheckedWord`), from ordinary code and from flat code alike.
|||
||| A `Bytes` is a record of one field, a buffer of `Data.Buffer`, which no
||| function of this module gives out, and which `generate` writes only
||| before the record exists. Idris erases a record of one field, so every
||| code generator holds a `Bytes` as its buffer: the native one as a
||| `BYTES` object (`Types.Kind`), which the contract states below, with
||| the record's immutability. The field is a `Uniform`, so that flat code
||| may hold a `Bytes`, one value as ordinary code holds it, where it may
||| not hold the buffer, whose type is external.
|||
||| Flat code reads a `Bytes` it is given, and makes none: `generate` runs a
||| function of ordinary code.
|||
||| Part of the type layer, the modules of `Types` (`Types.Kind` says what
||| it is).
module Native.Types.Bytes

-- lint: allow public-import: `uncheckedWord`'s and `generate`'s types,
-- written by the pure load's and the maker's types and a primitive's
-- signature, reduce only where they are visible, so they are wherever
-- this module is
import public Native.Primitive
import public Native.Types.FromWords
import public Native.Types.PureLoad

import Native.Types.Kind
import Native.Types.Repr

import Data.Buffer
import Native.Flat.Uniform as Flat

%default total

||| Words, made once and never written again.
export
record Bytes where
  constructor MkBytes
  buffer : Flat.Uniform Buffer

||| A `Bytes` is its buffer's object, a `BYTES` always,
public export
Only Kind.BYTES Bytes where

||| which no one writes once the `Bytes` exists.
public export
Immutable Bytes where

||| The words `f 0`, `f 1`, ..., `f (n - 1)`, none if `n` is not positive: the
||| maker of a `Bytes` (`Types.FromWords`), which states that its result is
||| the object of exactly those words. A function of ordinary code makes
||| each word, before the `Bytes` exists, so none of them can write it
||| after. The program ends for more words than fit in memory.
|||
||| It ends the program by the crash primitive in place, never by calling
||| `idris_crash`. Idris's Scheme backends, compiling a whole program,
||| keep a constant's value only if nothing it calls, directly or through
||| other functions, is a function whose whole body is a crash, as
||| `idris_crash`'s is; any other constant they compute again at each use.
||| So nothing in `generate` has a constant it makes, such as a table,
||| computed at each use: such a constant is made once, before `main`,
||| unless something else it calls, its words' function among them, calls
||| such a function. Chez's incremental code generator, which compiles a
||| program module by module, keeps no constant at all: each is computed
||| at each use.
export %noinline
generate : FromWords Bytes
generate n f =
  let m = max 0 n in
  -- lint: allow trust-escape: so many words do not fit in memory, and ending the program is
  -- all there is to do
  if m > maxWords then assert_total (prim__crash _ "idris: too many words for bytes") else
    -- lint: allow trust-escape: the buffer is made here, written only here, and given out only as
    -- the immutable record, after its last write
    unsafePerformIO $ do
      Just b <- newBuffer (8 * m)
        -- lint: allow trust-escape: a buffer of a size that is not negative is always made
        | Nothing => assert_total (prim__crash _ "idris: no buffer for bytes")
      fill b 0 (cast m)
      pure (MkBytes (Flat.MkUniform b))
  where
    -- word `i` of the rest, and the `left` words after it
    fill : Buffer -> (i : Int) -> (left : Nat) -> IO ()
    fill b i Z = pure ()
    fill b i (S left) = do
      setBits64 b (8 * i) (f i)
      fill b (i + 1) left

    ||| The most words a `Bytes` holds: so many that their bytes, 2^47, fill the
    ||| user address space of x86-64.
    maxWords : Int
    maxWords = 0x100000000000

||| Word `d` of row `i`, both in words: the word at `i + d`. Nothing checks
||| that it is inside, so each use says why it is (`trust-escape`); outside,
||| it is any word, or the end of the program. Natively it is one load,
||| inline in flat code; elsewhere its body, the buffer's word.
export %noinline
uncheckedWord : PureLoad Bytes (Primitive.signature Primitive.PayloadWord)
uncheckedWord (MkBytes (Flat.MkUniform b)) i d =
  -- lint: allow trust-escape: the buffer is never written once the record exists, so the read
  -- may be done at any time
  unsafePerformIO (getBits64 b (8 * (i + d)))
