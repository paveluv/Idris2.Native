||| The shapes of heap objects (`Shape`): what the collector knows of an
||| object, and all it knows. A shape says how many words an object has and
||| which of them hold values the collector must follow; which type the
||| object is, the collector never asks. Each type of object is laid out as
||| one shape, with a tag that tells it apart from the shape's other types
||| (`Types.Kind` gives each kind's), and the type's own part of the
||| header, which only code that knows the type reads.
|||
||| A header word is the shape's id in bits 0..3; flags in bits 4..7, which
||| the compiler always leaves 0 (the collector may use bit 4 as the mark bit
||| of a large space); the type's tag in bits 8..15; then the shape's counts
||| (`Field`), and above them the type's part:
|||
||| - `VALUES`: the number of values in bits 16..43, the part in 44..63.
||| - `RAW`: the number of bytes in bits 16..62, padded to words after the
|||   header, the part in bit 63. Bytes do not outgrow 47 bits, the user
|||   address space of x86-64, so a raw object that fits in memory fits its
|||   header.
||| - `MIXED`: the number of raw words in bits 16..19, then of values in
|||   20..47, the part in 48..63.
|||
||| No shape's id is 0, so a header's low four bits are never all zero: a
||| continuation, which has no header, begins with its 16-aligned resume
||| address, and is told apart by those bits being zero. Its size is in the
||| layout word before that address (`HeapObj.LayoutWord`): the fourth layout
||| the collector reads, the frame. Id 15 is the forwarding header, which the
||| collector writes over an object it has moved.
|||
||| A new shape is a change to the collector, and so to the runtime's core;
||| a new type of an existing shape is not.
|||
||| Part of the heap-object model, the modules of `HeapObj`: the contract
||| between compiled code and the runtime about objects, not part of
||| either, and so in the namespace of neither. It knows objects by their
||| shapes; which types there are, and how each is laid out as a shape, is
||| the type layer's (`Types.Kind`). Compiled code writes header words when
||| it allocates, and the collector reads shapes, sizes, scanned ranges and
||| continuation layouts. Every bit position and size rule is written down
||| once, here or in the type layer, and both sides take it from there. Its
||| modules import nothing from the compiler, so that the runtime's own
||| Idris can import them too.
module Native.HeapObj.Shape

%default total

||| The shapes of objects with a header.
public export
data Shape
  = ||| Values only, after the header.
    VALUES
  | ||| Raw bytes only, after the header, which the collector never reads.
    RAW
  | ||| Raw words, then values.
    MIXED

||| The shape's id, in bits 0..3 of a header word.
public export
shapeId : Shape -> Bits64
shapeId VALUES = 1
shapeId RAW = 2
shapeId MIXED = 3

||| The width of the id in a header word's low bits: a shape's, the
||| forwarding header's, or 0 for a continuation's resume address.
public export
idWidth : Bits64
idWidth = 4

||| The id in bits 0..3 of a forwarding header: the new address, 8-aligned,
||| in the rest of the word.
public export
forwardingId : Bits64
forwardingId = 15

||| The fields of a header word whose place the shape fixes: its counts,
||| the tag, and the type's part.
public export
data Field : Shape -> Type where
  Values : Field VALUES
  Bytes : Field RAW
  Raws : Field MIXED
  MixedValues : Field MIXED
  Tag : Field s
  Part : Field s

||| Where a field lives in the header word: its first bit and its width, as
||| the words the runtime's code shifts and masks by. This is the only place
||| the header word's layout is written down.
public export
place : {s : Shape} -> Field s -> (Bits64, Bits64)
place Values = (16, 28)
place Bytes = (16, 47)
place Raws = (16, 4)
place MixedValues = (20, 28)
place Tag = (8, 8)
place {s = VALUES} Part = (44, 20)
place {s = RAW} Part = (63, 1)
place {s = MIXED} Part = (48, 16)

||| An object's counts, as the compiler holds them: what its shape's fields
||| say. Raw bytes in whole words are counted as words.
public export
data Counts : Shape -> Type where
  ValuesOf : (values : Nat) -> Counts VALUES
  BytesOf : (bytes : Nat) -> Counts RAW
  WordsOf : (words : Nat) -> Counts RAW
  MixedOf : (raws, values : Nat) -> Counts MIXED

||| The number of words after the header.
public export
fieldWords : Counts s -> Nat
fieldWords (ValuesOf n) = n
fieldWords (BytesOf n) = byteWords n
  where
    ||| The words that so many bytes fill, padded to whole words.
    byteWords : Nat -> Nat
    byteWords n = cast ((the Integer (cast n) + 7) `div` 8)
fieldWords (WordsOf n) = n
fieldWords (MixedOf r n) = r + n

||| The collector's view: the word, counting the header as word 0, where the
||| values begin, and how many there are. Every other word is raw.
public export
scanned : Counts s -> (Nat, Nat)
scanned (ValuesOf n) = (1, n)
scanned (MixedOf r n) = (1 + r, n)
scanned _ = (1, 0)

||| A field of a header word. Inline, so that at a field written in the code
||| the shift and the mask are constants.
public export %inline
field : {s : Shape} -> Field s -> (header : Bits64) -> Bits64
field f h = prim__and_Bits64 (prim__shr_Bits64 h (fst (place f))) (prim__shl_Bits64 1 (snd (place f)) - 1)

||| A field's value where it lives in a header word: the word to add to a
||| header for it.
public export %inline
fieldBits : {s : Shape} -> Field s -> (value : Bits64) -> Bits64
fieldBits f v = prim__shl_Bits64 v (fst (place f))

||| Bits 0..3 of an object's first word: a shape's id, the forwarding id,
||| or 0 for a continuation.
public export %inline
shapeIdOf : (first : Bits64) -> Bits64
shapeIdOf h = prim__and_Bits64 h (prim__shl_Bits64 1 idWidth - 1)

||| Whether an object's first word is a continuation's resume address.
export
isFrame : (first : Bits64) -> Bool
isFrame h = shapeIdOf h == 0

export
forwardingHeader : (to : Bits64) -> Bits64
forwardingHeader to = prim__or_Bits64 (prim__shl_Bits64 to idWidth) forwardingId

export
isForwarding : (first : Bits64) -> Bool
isForwarding h = shapeIdOf h == forwardingId

export
forwardedTo : (header : Bits64) -> Bits64
forwardedTo h = prim__shr_Bits64 h idWidth

||| The words of an object with a header, the header included, by its header
||| word, as `fieldWords` gives them; 0 for a word that is no shape's.
export
objectWordsOf : (header : Bits64) -> Bits64
objectWordsOf h =
  let s = shapeIdOf h in
  if s == shapeId VALUES then 1 + field Values h
  else if s == shapeId RAW then 1 + byteWordsOf (field Bytes h)
  else if s == shapeId MIXED then 1 + field Raws h + field MixedValues h
  else 0
  where
    ||| The words that `bytes` fill, padded to whole words.
    %inline
    byteWordsOf : (bytes : Bits64) -> Bits64
    byteWordsOf b = prim__shr_Bits64 (b + 7) 3

||| The words of an object with a header that hold values, by its header
||| word, as `scanned` gives them: the first, and how many.
export
scannedOf : (header : Bits64) -> (Bits64, Bits64)
scannedOf h =
  let s = shapeIdOf h in
  if s == shapeId VALUES then (1, field Values h)
  else if s == shapeId MIXED then (1 + field Raws h, field MixedValues h)
  else (1, 0)
