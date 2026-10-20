||| The kinds of heap object (`Kind`), each with its layout, and each kind's
||| shape and tag, in the low bits of a header word.
|||
||| Part of the type layer, the modules of `Types`: the built-in types as
||| the heap-object model lays objects out (`HeapObj.Shape`), each kind a
||| shape and a tag, with their headers (`Types.Header`) and the encodings
||| of strings and bignums (`Types.Enc`). The code generator and the
||| runtime's support tier read it; the runtime's core, which knows objects
||| by their shapes alone, never does. It imports nothing from the compiler,
||| so that the runtime's own Idris can import it.
module Native.Types.Kind

import Decidable.Equality
import Decidable.Equality.Core
import Native.HeapObj.Shape as HeapObj

%default total

||| The kinds of heap object, each with its layout.
public export
data Kind
  = ||| A data constructor, with its global constructor id and its arity in
    ||| its header; field i, a `Val`, is at 8 + 8i. Fields are uniform even
    ||| where the declared field type is concrete.
    CON
  | ||| A partial application, with the function's arity and the number of
    ||| arguments filled so far, always fewer, in its header. The function's
    ||| code address is at 8, a raw word the collector does not scan;
    ||| argument i, a `Val`, is at 16 + 8i.
    CLOSURE
  | ||| A boxed 64-bit integer, for a value outside the fixnum range: its bit
    ||| pattern at 8. Signedness is static, not stored.
    INT64
  | ||| A boxed double: its IEEE 754 binary64 bits at 8.
    DOUBLE
  | ||| A string, with its length in bytes in its header: the bytes from 8,
    ||| with no terminator, padded to a multiple of 8.
    STRING
  | ||| An integer outside the small range, as the program's bignum encoding
    ||| lays it out (`BignumEnc`): its limbs from 8, and in its header
    ||| the number of words they fill, and the sign where the encoding keeps
    ||| it there. A `BIGNUM` never holds a value in the small range, and its
    ||| top word is never redundant (zero, or under two's complement the sign
    ||| extension of the word below), so equality is structural.
    BIGNUM
  | ||| A mutable reference: one `Val` at 8.
    IOREF
  | ||| A mutable array, with its number of elements in its header: element
    ||| i, a `Val`, at 8 + 8i.
    ARRAY
  | ||| A mutable record (`Native.Types.Struct`): with its numbers of raw
    ||| words and of values in its header, the raw words at 8, which the
    ||| collector does not scan, then the values, `Val`s.
    STRUCT
  | ||| A byte buffer, laid out as a `STRING`, without the claim of an
    ||| encoding.
    BUFFER
  | ||| A foreign pointer: one raw word at 8, which the collector never
    ||| follows.
    PTR
  | ||| A continuation: a suspended call, under the heap lowering. It has no
    ||| header word, so there is no `Header enc CONT`. Word 0 is the code address
    ||| where execution resumes, 16-aligned; the parent continuation, a `Val`,
    ||| is at 8; the live `Val`s follow from 16, then the live raw words. The
    ||| word just before the resume code in the text is the layout word: the
    ||| number of live `Val`s in bits 0..23, of raw words in bits 24..47, and
    ||| the magic 0x1DC0 in bits 48..63. A continuation is immutable once
    ||| initialised. Only the rendering of `Call` and `Apply` makes one.
    CONT

||| The shape a kind's objects have (`HeapObj.Shape`); a continuation has no
||| header, and so no shape.
public export
shape : Kind -> Maybe HeapObj.Shape
shape CON = Just HeapObj.Shape.VALUES
shape IOREF = Just HeapObj.Shape.VALUES
shape ARRAY = Just HeapObj.Shape.VALUES
shape CLOSURE = Just HeapObj.Shape.MIXED
shape STRUCT = Just HeapObj.Shape.MIXED
shape INT64 = Just HeapObj.Shape.RAW
shape DOUBLE = Just HeapObj.Shape.RAW
shape PTR = Just HeapObj.Shape.RAW
shape STRING = Just HeapObj.Shape.RAW
shape BUFFER = Just HeapObj.Shape.RAW
shape BIGNUM = Just HeapObj.Shape.RAW
shape CONT = Nothing

||| The kind's tag, which tells it apart from the other kinds of its shape.
public export
tag : Kind -> Bits64
tag CON = 0
tag IOREF = 1
tag ARRAY = 2
tag CLOSURE = 0
tag STRUCT = 1
tag INT64 = 0
tag DOUBLE = 1
tag PTR = 2
tag STRING = 3
tag BUFFER = 4
tag BIGNUM = 5
tag CONT = 0

||| The kind's code: bits 0..15 of each of its headers, its shape's id and
||| its tag with the flags 0, as the word the runtime's code compares them
||| with; 0 for a continuation, whose first word has bits 0..3 zero.
public export
code : Kind -> Bits64
code k =
  maybe 0 (\s => HeapObj.Shape.shapeId s + HeapObj.Shape.fieldBits {s} HeapObj.Shape.Tag (tag k))
    (shape k)

||| The kind with this code, if any.
public export
fromCode : Bits64 -> Maybe Kind
fromCode 0x001 = Just CON
fromCode 0x101 = Just IOREF
fromCode 0x201 = Just ARRAY
fromCode 0x003 = Just CLOSURE
fromCode 0x103 = Just STRUCT
fromCode 0x002 = Just INT64
fromCode 0x102 = Just DOUBLE
fromCode 0x202 = Just PTR
fromCode 0x302 = Just STRING
fromCode 0x402 = Just BUFFER
fromCode 0x502 = Just BIGNUM
fromCode 0 = Just CONT
fromCode _ = Nothing

public export
Eq Kind where
  a == b = code a == code b

||| Equal kinds have equal codes, since `fromCode` inverts `code`.
public export
DecEq Kind where
  decEq a b = case decEq (code a) (code b) of
    Yes p =>
      Yes
        (justInjective
         (trans (sym (kindRoundTrip a)) (trans (cong fromCode p) (kindRoundTrip b))))
    No c => No (\q => c (cong code q))
    where
      kindRoundTrip : (k : Kind) -> fromCode (code k) = Just k
      kindRoundTrip CON = Refl
      kindRoundTrip CLOSURE = Refl
      kindRoundTrip INT64 = Refl
      kindRoundTrip DOUBLE = Refl
      kindRoundTrip STRING = Refl
      kindRoundTrip BIGNUM = Refl
      kindRoundTrip IOREF = Refl
      kindRoundTrip ARRAY = Refl
      kindRoundTrip STRUCT = Refl
      kindRoundTrip BUFFER = Refl
      kindRoundTrip PTR = Refl
      kindRoundTrip CONT = Refl

      justInjective : Just a' = Just b' -> a' = b'
      justInjective Refl = Refl

public export
Show Kind where
  show CON = "CON"
  show CLOSURE = "CLOSURE"
  show INT64 = "INT64"
  show DOUBLE = "DOUBLE"
  show STRING = "STRING"
  show BIGNUM = "BIGNUM"
  show IOREF = "IOREF"
  show ARRAY = "ARRAY"
  show STRUCT = "STRUCT"
  show BUFFER = "BUFFER"
  show PTR = "PTR"
  show CONT = "CONT"

||| A header word's kind code, as `code` gives a kind's: its shape's id, in
||| bits 0..3, and its tag, the flags between them left out, as the
||| collector may set its mark there.
public export %inline
headerCode : (header : Bits64) -> Bits64
headerCode h =
  HeapObj.Shape.headerShapeId h
    + HeapObj.Shape.fieldBits {s = HeapObj.Shape.VALUES} HeapObj.Shape.Tag
        (HeapObj.Shape.field {s = HeapObj.Shape.VALUES} HeapObj.Shape.Tag h)
