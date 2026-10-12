||| The heap-object model: the program's encodings, what an object is in
||| memory under them, and how a uniform value is a word. It is the contract
||| between compiled code and the runtime, not part of either: compiled code
||| writes header words when it allocates and reads constructor ids in a
||| `case`, the runtime's `idris_apply` edits closure headers, and the
||| collector reads kinds, sizes, scanned ranges and continuation layouts.
||| Every bit position and size rule is written down here once, and both
||| sides take it from here. The module imports nothing from the compiler, so
||| that the runtime's own Idris can import it too.
module Compiler.Native.HeapObject

import public Decidable.Equality

import Data.List

%default total

------------------------------------------------------------------------------
-- Enc
--
-- How each sort of data that compiled code and the runtime share is laid out
-- in words is a choice made once per compilation: an encoding. A program and
-- its runtime must agree on every one, so the IR, every pass that depends on
-- one, and the headers below are indexed by the program's encodings
-- (`Enc`).

||| How a uniform value is a word ("Uniform values as words", below).
public export
data ValEnc
  = ||| Fixnum tag 1: fixnum n is the word 2n + 1, and a pointer is the
    ||| object's address.
    FixnumTag1
  | ||| Fixnum tag 0: fixnum n is the word 2n, and a pointer is the object's
    ||| address plus 1, so a load or store through it folds the -1 into its
    ||| displacement.
    FixnumTag0
  | ||| No fixnums: every integer in a uniform position is a boxed object,
    ||| and a pointer is the object's address, its low three bits free.
    NoFixnums

public export
Eq ValEnc where
  FixnumTag1 == FixnumTag1 = True
  FixnumTag0 == FixnumTag0 = True
  NoFixnums == NoFixnums = True
  _ == _ = False

public export
Show ValEnc where
  show FixnumTag1 = "FixnumTag1"
  show FixnumTag0 = "FixnumTag0"
  show NoFixnums = "NoFixnums"

||| The value encodings with fixnums: those under which a fixnum, and the
||| IR's tagging instructions, exist.
public export
data HasFixnums : ValEnc -> Type where
  Tag1 : HasFixnums FixnumTag1
  Tag0 : HasFixnums FixnumTag0

public export
Uninhabited (HasFixnums NoFixnums) where
  uninhabited Tag1 impossible
  uninhabited Tag0 impossible

||| How many bits a limb holds. A `BIGNUM`'s limbs are its digits in base 2
||| to that power, least significant first, packed into its words from the
||| low end: one to a word, or two, the lower limb in the word's low half.
public export
data LimbWidth = Limb64 | Limb32

||| How a `BIGNUM` holds its sign.
public export
data BignumSign
  = ||| A sign bit in the header, and the magnitude in the limbs, as in GMP
    ||| and CPython.
    SignMagnitude
  | ||| The limbs hold the value in two's complement, the top limb's top bit
    ||| its sign, as in SBCL.
    TwosComplement

||| How an integer outside the small range is a `BIGNUM`. The small range is
||| the fixnum range under a value encoding with fixnums, and empty under
||| `NoFixnums`, where every integer is a `BIGNUM`.
public export
record BignumEnc where
  constructor MkBignumEnc
  limbWidth : LimbWidth
  sign : BignumSign

||| The bignum encodings whose header holds the sign: those under which a
||| `BignumH` exists.
public export
data SignInHeader : BignumEnc -> Type where
  IsSignMagnitude : SignInHeader (MkBignumEnc w SignMagnitude)

||| Whether a bignum encoding keeps the sign in the header, with the proof
||| that it does.
public export
signInHeader : (b : BignumEnc) -> Maybe (SignInHeader b)
signInHeader (MkBignumEnc _ SignMagnitude) = Just IsSignMagnitude
signInHeader (MkBignumEnc _ TwosComplement) = Nothing

||| The words a `BIGNUM`'s limbs fill for a magnitude, least significant
||| first, none of them a zero at the top: the same under either limb width,
||| since two 32-bit limbs fill a word as one 64-bit limb does.
public export covering
magnitudeWords : Integer -> List Int64
magnitudeWords m =
  if m <= 0 then [] else word (m `mod` 18446744073709551616) :: magnitudeWords (m `div` 18446744073709551616)
  where
    word : Integer -> Int64
    word u = cast (if u >= 9223372036854775808 then u - 18446744073709551616 else u)

||| How a `String` is laid out: its payload, and the parts of its header.
||| Every `STRING` holds a well-formed encoding of a sequence of Unicode
||| scalar values (no surrogates, nothing above U+10FFFF, and for UTF-8 the
||| shortest form), which every operation that makes a string keeps and every
||| one that reads it relies on. Code that branches on the encoding matches
||| every constructor, with no catch-all, so that another encoding is a
||| constructor the typechecker finds every place for.
public export
data StringEncoding
  = ||| The UTF-8 bytes, and a header bit set exactly when every byte is
    ||| below 0x80, which turns the code-point operations of an ASCII string
    ||| into byte operations.
    Utf8
  | ||| One 32-bit code point per character, Chez's layout.
    Utf32

||| The string encodings under which a `StringH` exists, with the proof.
public export
data Utf8Strings : StringEncoding -> Type where
  IsUtf8 : Utf8Strings Utf8

||| The string encodings under which a `StringCharsH` exists.
public export
data Utf32Strings : StringEncoding -> Type where
  IsUtf32 : Utf32Strings Utf32

||| The encodings a program is compiled with. Only encodings belong here; a
||| choice that does not change how data is laid out, such as an
||| optimisation, is a setting of the compilation instead.
|||
||| Code that branches on an encoding matches the record, uses `with`, or
||| calls a function of the encoding such as `fixnumTag`: a `case` on a
||| projection does not refine a proof about it, such as
||| `HasFixnums enc.val`.
public export
record Enc where
  constructor MkEnc
  ||| How a uniform value is a word.
  val : ValEnc
  ||| How an integer outside the small range is a `BIGNUM`.
  bignum : BignumEnc
  ||| How a `String` is laid out.
  strings : StringEncoding

||| The encodings a program is compiled with unless directed otherwise:
||| fixnum tag 1, bignums of 64-bit limbs holding the magnitude, with the
||| sign in the header, and UTF-8 strings.
public export
defaultEnc : Enc
defaultEnc = MkEnc FixnumTag1 (MkBignumEnc Limb64 SignMagnitude) Utf8

------------------------------------------------------------------------------
-- Heap objects
--
-- Every heap object is 8-byte aligned and begins with one header word, which
-- says what the object is: its kind, and the parts of its header, whose
-- number and meaning depend on the kind (`Header`). The words after the
-- header are the object's fields; offsets below are in bytes from the start
-- of the object. The header alone gives the object's size and which of its
-- fields the collector scans (`objectWords`, `scanned`); the collector needs
-- nothing else. The exception is `CONT`, which has no header word.
--
-- The header word: the kind's id in bits 0..3; flags in bits 4..7, which the
-- compiler always leaves 0 (the collector uses bit 4 as the mark bit of the
-- large space during a full collection); from bit 8, the header's parts,
-- laid out per kind (`place`).
--
-- Static objects (`Static` in `Compiler.Native.LocatedIR`) have exactly the same
-- layouts.

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

||| An encoding has at most one proof that it has fixnums.
public export
0 fixnumsUnique : (p, q : HasFixnums v) -> p = q
fixnumsUnique Tag1 Tag1 = Refl
fixnumsUnique Tag0 Tag0 = Refl

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

||| What a header says, per kind and under the program's encodings: one
||| constructor for each kind that has a header, whose arguments are the
||| header's parts, named for their meaning. No constructor makes a
||| `Header enc CONT`, since a continuation has no header. A `BIGNUM`'s header
||| depends on its bignum encoding; only the sign-magnitude one exists so far.
public export
data Header : Enc -> Kind -> Type where
  ConH     : (conId : Nat) -> (arity : Nat) -> Header enc CON
  ClosureH : (arity : Nat) -> (filled : Nat) -> Header enc CLOSURE
  Int64H   : Header enc INT64
  DoubleH  : Header enc DOUBLE
  StringH  : {auto 0 u : Utf8Strings enc.strings} -> (ascii : Bool) -> (bytes : Nat) -> Header enc STRING
  StringCharsH : {auto 0 u : Utf32Strings enc.strings} -> (chars : Nat) -> Header enc STRING
  BignumH  : {auto 0 sh : SignInHeader enc.bignum} -> (negative : Bool) -> (words : Nat) ->
             Header enc BIGNUM
  IORefH   : Header enc IOREF
  ArrayH   : (elems : Nat) -> Header enc ARRAY
  BufferH  : (bytes : Nat) -> Header enc BUFFER
  PtrH     : Header enc PTR

||| A continuation has no header.
public export
Uninhabited (Header enc CONT) where
  uninhabited (ConH _ _) impossible
  uninhabited (ClosureH _ _) impossible
  uninhabited Int64H impossible
  uninhabited DoubleH impossible
  uninhabited (StringH _ _) impossible
  uninhabited (StringCharsH _) impossible
  uninhabited (BignumH _ _) impossible
  uninhabited IORefH impossible
  uninhabited (ArrayH _) impossible
  uninhabited (BufferH _) impossible
  uninhabited PtrH impossible

||| Two to the power, as an `Integer`. Public so that `partUnit` and `fits`,
||| which are, reduce outside this module: a header's fit can then be
||| decided where the header is written.
public export
pow2 : Nat -> Integer
pow2 Z = 1
pow2 (S n) = 2 * pow2 n

||| A part of a header, by kind: what `LoadPart` reads.
public export
data HeaderPart : Kind -> Type where
  ConId          : HeaderPart CON
  ConArity       : HeaderPart CON
  ClosureArity   : HeaderPart CLOSURE
  ClosureFilled  : HeaderPart CLOSURE
  StringAscii    : HeaderPart STRING
  StringBytes    : HeaderPart STRING
  StringChars    : HeaderPart STRING
  BignumNegative : HeaderPart BIGNUM
  BignumWords    : HeaderPart BIGNUM
  ArrayElems     : HeaderPart ARRAY
  BufferBytes    : HeaderPart BUFFER

||| Where a part lives in the header word: its first bit and its width, as
||| the words the runtime's code shifts and masks by. This
||| is the only place the bit layout is written down; encoding, decoding,
||| the rendering of `LoadPart` and the seed's `idris_apply` all read it here. A kind's parts lie in bits
||| 8..63 and do not overlap.
public export
place : {0 k : Kind} -> HeaderPart k -> (Bits64, Bits64)
place ConId = (8, 28)
place ConArity = (36, 28)
place ClosureArity = (8, 28)
place ClosureFilled = (36, 28)
place StringAscii = (8, 1)
place StringBytes = (9, 55)
place StringChars = (8, 56)
place BignumNegative = (8, 1)
place BignumWords = (9, 55)
place ArrayElems = (8, 56)
place BufferBytes = (8, 56)

||| What adding one to a part adds to the header word: a closure with one
||| more argument filled is its header plus `partUnit ClosureFilled`.
public export
partUnit : {0 k : Kind} -> HeaderPart k -> Integer
partUnit p = pow2 (cast (fst (place p)))

public export
Show (HeaderPart kn) where
  show ConId = "ConId"
  show ConArity = "ConArity"
  show ClosureArity = "ClosureArity"
  show ClosureFilled = "ClosureFilled"
  show StringAscii = "StringAscii"
  show StringBytes = "StringBytes"
  show StringChars = "StringChars"
  show BignumNegative = "BignumNegative"
  show BignumWords = "BignumWords"
  show ArrayElems = "ArrayElems"
  show BufferBytes = "BufferBytes"

||| A header's parts with their values, in order.
public export
parts : {0 k : Kind} -> Header enc k -> List (HeaderPart k, Nat)
parts (ConH c a) = [(ConId, c), (ConArity, a)]
parts (ClosureH a f) = [(ClosureArity, a), (ClosureFilled, f)]
parts (StringH a n) = [(StringAscii, if a then 1 else 0), (StringBytes, n)]
parts (StringCharsH n) = [(StringChars, n)]
parts (BignumH neg n) = [(BignumNegative, if neg then 1 else 0), (BignumWords, n)]
parts (ArrayH n) = [(ArrayElems, n)]
parts (BufferH n) = [(BufferBytes, n)]
parts Int64H = []
parts DoubleH = []
parts IORefH = []
parts PtrH = []

public export
{kn : Kind} -> Show (Header enc kn) where
  show h = show kn ++ concatMap (\pv => " " ++ show (fst pv) ++ "=" ++ show (snd pv)) (parts h)

||| Whether two headers, of any kinds, are the same header.
public export
sameHeader : {k, k' : Kind} -> Header enc k -> Header enc k' -> Bool
sameHeader h h' = k == k' && map snd (parts h) == map snd (parts h')

||| Whether every part fits its width. Every header the IR carries comes with
||| the proof (`Compiler.Native.TermIR.wellFormed`); encoding a header that does
||| not fit loses the high bits of the part, and never touches its neighbours.
public export
fits : {0 k : Kind} -> Header enc k -> Bool
fits h = all (\pv => cast (snd pv) < pow2 (cast (snd (place (fst pv))))) (parts h)

unsigned : Int64 -> Integer
unsigned w = if w < 0 then cast w + pow2 64 else cast w

signed : Integer -> Int64
signed u = cast (if u >= pow2 63 then u - pow2 64 else u)

||| The header word, with flags 0.
export
encodeHeader : {k : Kind} -> Header enc k -> Int64
encodeHeader h = signed (cast (kindId k) + sum (map part (parts h)))
  where
    part : (HeaderPart k', Nat) -> Integer
    part (p, v) = (cast v `mod` pow2 (cast (snd (place p)))) * pow2 (cast (fst (place p)))

||| The header a word encodes, if the word is exactly what `encodeHeader`
||| makes of some header: a kind's id other than `CONT`'s, flags 0, and no
||| bit outside the kind's parts. So `decodeHeader w = Just (k ** h)` implies
||| `encodeHeader h = w`, and for a header that fits,
||| `decodeHeader (encodeHeader h)` gives the header back, which
||| `tests/native/header001` checks for every part at its boundaries.
export
decodeHeader : (enc : Enc) -> Int64 -> Maybe (k : Kind ** Header enc k)
decodeHeader enc w = do
  r <- parse (kindOfId (cast (u `mod` 16)))
  if encodeHeader (snd r) == w then Just r else Nothing
  where
    u : Integer
    u = unsigned w

    get : HeaderPart k' -> Nat
    get p = cast ((u `div` pow2 (cast (fst (place p)))) `mod` pow2 (cast (snd (place p))))

    -- A sign-magnitude program's BIGNUM header, matched on the record so
    -- that the match proves the sign is in the header.
    bignum : (enc' : Enc) -> Maybe (k : Kind ** Header enc' k)
    bignum (MkEnc _ (MkBignumEnc _ SignMagnitude) _) =
      Just (BIGNUM ** BignumH (get BignumNegative == 1) (get BignumWords))
    bignum _ = Nothing

    -- A string's header, matched on the record so that the match proves the
    -- encoding the constructor needs.
    string : (enc' : Enc) -> Maybe (k : Kind ** Header enc' k)
    string (MkEnc _ _ Utf8) = Just (STRING ** StringH (get StringAscii == 1) (get StringBytes))
    string (MkEnc _ _ Utf32) = Just (STRING ** StringCharsH (get StringChars))

    parse : Maybe Kind -> Maybe (k : Kind ** Header enc k)
    parse (Just CON) = Just (CON ** ConH (get ConId) (get ConArity))
    parse (Just CLOSURE) = Just (CLOSURE ** ClosureH (get ClosureArity) (get ClosureFilled))
    parse (Just INT64) = Just (INT64 ** Int64H)
    parse (Just DOUBLE) = Just (DOUBLE ** DoubleH)
    parse (Just STRING) = string enc
    parse (Just BIGNUM) = bignum enc
    parse (Just IOREF) = Just (IOREF ** IORefH)
    parse (Just ARRAY) = Just (ARRAY ** ArrayH (get ArrayElems))
    parse (Just BUFFER) = Just (BUFFER ** BufferH (get BufferBytes))
    parse (Just PTR) = Just (PTR ** PtrH)
    parse (Just CONT) = Nothing
    parse Nothing = Nothing

||| The words needed for so many bytes.
public export
byteWords : Nat -> Nat
byteWords n = cast ((the Integer (cast n) + 7) `div` 8)

||| The number of fields: the object's words after its header.
public export
fieldWords : {0 k : Kind} -> Header enc k -> Nat
fieldWords (ConH _ a) = a
fieldWords (ClosureH _ f) = 1 + f
fieldWords Int64H = 1
fieldWords DoubleH = 1
fieldWords (StringH _ n) = byteWords n
fieldWords (StringCharsH n) = byteWords (4 * n)
fieldWords (BignumH _ n) = n
fieldWords IORefH = 1
fieldWords (ArrayH n) = n
fieldWords (BufferH n) = byteWords n
fieldWords PtrH = 1

||| The object's size in words, its header included.
public export
objectWords : {0 k : Kind} -> Header enc k -> Nat
objectWords h = 1 + fieldWords h

||| The collector's view: the word, counting the header as word 0, where the
||| scanned fields begin, and how many there are. Every other field is raw.
public export
scanned : {0 k : Kind} -> Header enc k -> (Nat, Nat)
scanned (ConH _ a) = (1, a)
scanned (ClosureH _ f) = (2, f)
scanned IORefH = (1, 1)
scanned (ArrayH n) = (1, n)
scanned _ = (1, 0)

||| The layout word that precedes every resume point in the text: the number
||| of live `Val`s in bits 0..23, of live raw words in bits 24..47, and the
||| magic 0x1DC0 in bits 48..63. A continuation has no header word; its first
||| word is its resume address, and the word before that address gives its
||| size (`CONT`).
public export
layoutWord : (nval, nraw : Integer) -> Integer
layoutWord nval nraw = 0x1DC0000000000000 + nraw * 0x1000000 + nval

------------------------------------------------------------------------------
-- Uniform values as words
--
-- A uniform value (`Val` in `Compiler.Native.LocatedIR`) is one word: a fixnum, a
-- pointer to an object, or the erased value. How each is a word is the value
-- encoding (`ValEnc`, above), one of the program's encodings. Objects
-- are 8-byte aligned, so an object's address has its low three bits 0, which
-- leaves room for a tag in the word.
--
-- The erased value stands wherever Idris erased something but a word is
-- still passed (quantity-0 arguments, the `%World` token, types). No code
-- inspects it, and it is never dereferenced, so under an encoding with
-- fixnums it is simply fixnum 0.
--
-- An integer outside the fixnum range, and under `NoFixnums` every integer,
-- is a boxed object (`INT64`, `BIGNUM`). The renderings carry the encoding
-- out in their `Tag`, `Untag`, `TagOv` and `IsFixnum`, in their arithmetic,
-- comparisons and switches on fixnums, and in the pointer tag of every load
-- and store through a pointer.

||| The fixnum tag of an encoding with fixnums: fixnum n is the word 2n plus
||| it.
public export
fixnumTag : (venc : ValEnc) -> {auto 0 fx : HasFixnums venc} -> Integer
fixnumTag FixnumTag1 = 1
fixnumTag FixnumTag0 = 0

||| What a pointer word adds to the object's address.
public export
pointerTag : ValEnc -> Integer
pointerTag FixnumTag1 = 0
pointerTag FixnumTag0 = 1
pointerTag NoFixnums = 0

||| The smallest and the largest fixnum, under either encoding with fixnums.
public export
fixnumMin, fixnumMax : Integer
fixnumMin = -4611686018427387904
fixnumMax = 4611686018427387903

||| Whether an integer is in the fixnum range.
public export
inFixnumRange : Integer -> Bool
inFixnumRange v = v >= fixnumMin && v <= fixnumMax

||| The word of the uniform value that is this integer, where there is one: a
||| fixnum under an encoding with fixnums; under `NoFixnums`, where integers
||| are boxed, only 0, the erased value. An immediate in a `Val` position
||| means the integer, and the rendering takes its word from here.
public export
valWord : ValEnc -> Integer -> Maybe Int64
valWord FixnumTag1 v = if inFixnumRange v then Just (cast (2 * v + 1)) else Nothing
valWord FixnumTag0 v = if inFixnumRange v then Just (cast (2 * v)) else Nothing
valWord NoFixnums v = if v == 0 then Just 0 else Nothing

||| The erased value's word: fixnum 0's under an encoding with fixnums, the
||| word 0 under `NoFixnums`.
public export
erasedWord : ValEnc -> Int64
erasedWord FixnumTag1 = 1
erasedWord FixnumTag0 = 0
erasedWord NoFixnums = 0

||| Whether a word is a fixnum's.
public export
isFixnumWord : ValEnc -> Int64 -> Bool
isFixnumWord FixnumTag1 w = mod (abs (the Integer (cast w))) 2 == 1
isFixnumWord FixnumTag0 w = mod (abs (the Integer (cast w))) 2 == 0
isFixnumWord NoFixnums _ = False
