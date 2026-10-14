||| The kinds of heap object (`Kind`), each with its layout, and each kind's
||| id, in the low bits of a header word.
|||
||| Part of the heap-object model, the contract between compiled code and the
||| runtime (`Compiler.Native.HeapObject.Enc` says what it is): it imports
||| nothing from the compiler, so that the runtime's own Idris can import it.
module Compiler.Native.HeapObject.Kind

import Decidable.Equality

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

||| The kind's id, in bits 0..3 of a header word, as the word the runtime's
||| code compares it with. Every id is between 1 and
||| 15, so a header word's low four bits are never all zero; a continuation's
||| word 0, a 16-aligned code address, has them all zero, which is how a
||| `CONT` is told apart from an object with a header. Id 15 is reserved for
||| the forwarding header a copying collector writes over an object it has
||| moved; 12 to 14 are free.
public export
kindId : Kind -> Bits64
kindId CON = 1
kindId CLOSURE = 2
kindId INT64 = 3
kindId DOUBLE = 4
kindId STRING = 5
kindId BIGNUM = 6
kindId IOREF = 7
kindId ARRAY = 8
kindId BUFFER = 9
kindId PTR = 10
kindId CONT = 11

||| The kind with this id, if any.
public export
kindOfId : Bits64 -> Maybe Kind
kindOfId 1 = Just CON
kindOfId 2 = Just CLOSURE
kindOfId 3 = Just INT64
kindOfId 4 = Just DOUBLE
kindOfId 5 = Just STRING
kindOfId 6 = Just BIGNUM
kindOfId 7 = Just IOREF
kindOfId 8 = Just ARRAY
kindOfId 9 = Just BUFFER
kindOfId 10 = Just PTR
kindOfId 11 = Just CONT
kindOfId _ = Nothing

public export
Eq Kind where
  a == b = kindId a == kindId b

kindRoundTrip : (k : Kind) -> kindOfId (kindId k) = Just k
kindRoundTrip CON = Refl
kindRoundTrip CLOSURE = Refl
kindRoundTrip INT64 = Refl
kindRoundTrip DOUBLE = Refl
kindRoundTrip STRING = Refl
kindRoundTrip BIGNUM = Refl
kindRoundTrip IOREF = Refl
kindRoundTrip ARRAY = Refl
kindRoundTrip BUFFER = Refl
kindRoundTrip PTR = Refl
kindRoundTrip CONT = Refl

justInjective : Just a = Just b -> a = b
justInjective Refl = Refl

||| Equal kinds have equal ids, since `kindOfId` inverts `kindId`.
public export
DecEq Kind where
  decEq a b = case decEq (kindId a) (kindId b) of
    Yes p => Yes (justInjective (trans (sym (kindRoundTrip a)) (trans (cong kindOfId p) (kindRoundTrip b))))
    No c => No (\q => c (cong kindId q))

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
  show BUFFER = "BUFFER"
  show PTR = "PTR"
  show CONT = "CONT"
