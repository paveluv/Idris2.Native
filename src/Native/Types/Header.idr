||| What an object is in memory: its header (`Header`), and the sizes and
||| scanned fields the header gives.
|||
||| Every heap object is 8-byte aligned and begins with one header word,
||| which says what the object is: its kind (`Types.Kind`), and the parts
||| of its header, whose number and meaning depend on the kind. The words
||| after the header are the object's fields; offsets below are in bytes
||| from the start of the object. The exception is `CONT`, which has no
||| header word.
|||
||| A header word is laid out by the kind's shape (`HeapObj.Shape`): the
||| shape's id and the kind's tag (the kind's `code`), the shape's counts,
||| which are parts of the header or fixed by the kind (`fixedWord`), and
||| the kind's own parts in the shape's `Part` field (`place`). So the
||| header alone gives the object's size and which of its fields the
||| collector scans (`objectWords`, `scanned`), by its shape (`counts`).
|||
||| Static objects (`Native.Codegen.LocatedIR.Static`) have exactly the
||| same layouts.
|||
||| Part of the type layer, the modules of `Types` (`Types.Kind` says what
||| it is): it imports nothing from the compiler, so that the runtime's own
||| Idris can import it.
module Native.Types.Header

import Native.Types.BignumEnc
import Native.Types.Enc
import Native.Types.Kind
import Native.Types.StringEnc

import Data.Maybe
import Native.HeapObj.Shape as HeapObj

%default total

||| What a header says, per kind and under the program's encodings: one
||| constructor for each kind that has a header (`Kind.Headed`), whose
||| arguments are the header's parts, named for their meaning. A string's
||| and a `BIGNUM`'s parts are their encodings' (`StringParts`,
||| `BignumParts`), so that another encoding adds a case there, not a
||| constructor here; only the sign-magnitude `BIGNUM` has a header so far.
public export
data Header : Enc -> Kind -> Type where
  ConH     : (conId : Nat) -> (arity : Nat) -> Header enc Kind.CON
  ClosureH : (arity : Nat) -> (filled : Nat) -> Header enc Kind.CLOSURE
  Int64H   : Header enc Kind.INT64
  DoubleH  : Header enc Kind.DOUBLE
  StringH  : StringEnc.StringParts enc.string -> Header enc Kind.STRING
  BignumH  : BignumEnc.BignumParts enc.bignum -> Header enc Kind.BIGNUM
  IORefH   : Header enc Kind.IOREF
  ArrayH   : (elems : Nat) -> Header enc Kind.ARRAY
  StructH  : (raws : Nat) -> (values : Nat) -> Header enc Kind.STRUCT
  BytesH   : (bytes : Nat) -> Header enc Kind.BYTES
  PtrH     : Header enc Kind.PTR

||| A part of a header, by kind: what `LoadPart` reads.
public export
data HeaderPart : Kind -> Type where
  ConIdP          : HeaderPart Kind.CON
  ConArityP       : HeaderPart Kind.CON
  ClosureArityP   : HeaderPart Kind.CLOSURE
  ClosureFilledP  : HeaderPart Kind.CLOSURE
  StringAsciiP    : HeaderPart Kind.STRING
  StringBytesP    : HeaderPart Kind.STRING
  StringCharsP    : HeaderPart Kind.STRING
  BignumNegativeP : HeaderPart Kind.BIGNUM
  BignumWordsP    : HeaderPart Kind.BIGNUM
  ArrayElemsP     : HeaderPart Kind.ARRAY
  StructRawsP     : HeaderPart Kind.STRUCT
  StructValuesP   : HeaderPart Kind.STRUCT
  BytesLengthP    : HeaderPart Kind.BYTES

public export
Show (HeaderPart kn) where
  show ConIdP = "ConIdP"
  show ConArityP = "ConArityP"
  show ClosureArityP = "ClosureArityP"
  show ClosureFilledP = "ClosureFilledP"
  show StringAsciiP = "StringAsciiP"
  show StringBytesP = "StringBytesP"
  show StringCharsP = "StringCharsP"
  show BignumNegativeP = "BignumNegativeP"
  show BignumWordsP = "BignumWordsP"
  show ArrayElemsP = "ArrayElemsP"
  show StructRawsP = "StructRawsP"
  show StructValuesP = "StructValuesP"
  show BytesLengthP = "BytesLengthP"

||| A header's parts with their values, in order.
public export
parts : {enc : Enc} -> {0 k : Kind} -> Header enc k -> List (HeaderPart k, Nat)
parts (ConH c a) = [(ConIdP, c), (ConArityP, a)]
parts (ClosureH a f) = [(ClosureArityP, a), (ClosureFilledP, f)]
parts (StringH p) = strings enc.string p
  where
    strings : (s : StringEnc) -> StringEnc.StringParts s -> List (HeaderPart Kind.STRING, Nat)
    strings StringEnc.Utf8 q = [(StringAsciiP, if q.ascii then 1 else 0), (StringBytesP, q.bytes)]
    strings StringEnc.Utf32 q = [(StringCharsP, q.chars)]
parts (BignumH p) = bignums enc.bignum p
  where
    bignums : (b : BignumEnc) -> BignumEnc.BignumParts b -> List (HeaderPart Kind.BIGNUM, Nat)
    bignums (MkBignumEnc _ BignumEnc.SignMagnitude) q =
      [(BignumNegativeP, if q.negative then 1 else 0), (BignumWordsP, q.words)]
    bignums (MkBignumEnc _ BignumEnc.TwosComplement) q = absurd q
parts (ArrayH n) = [(ArrayElemsP, n)]
parts (StructH r v) = [(StructRawsP, r), (StructValuesP, v)]
parts (BytesH n) = [(BytesLengthP, n)]
parts Int64H = []
parts DoubleH = []
parts IORefH = []
parts PtrH = []

public export
{enc : Enc} -> {kn : Kind} -> Show (Header enc kn) where
  show h = show kn ++ concatMap (\pv => " " ++ show (fst pv) ++ "=" ++ show (snd pv)) (parts h)

||| A header's kind has one.
public export
headed : Header enc k -> Kind.Headed k
headed (ConH _ _) = ItIsJust
headed (ClosureH _ _) = ItIsJust
headed Int64H = ItIsJust
headed DoubleH = ItIsJust
headed (StringH _) = ItIsJust
headed (BignumH _) = ItIsJust
headed IORefH = ItIsJust
headed (ArrayH _) = ItIsJust
headed (StructH _ _) = ItIsJust
headed (BytesH _) = ItIsJust
headed PtrH = ItIsJust

||| Where a part lives in the header word: its first bit and its width, as
||| the words the runtime's code shifts and masks by: a field of the kind's
||| shape (`Shape.place`), or a count of whole units of a shape's count of
||| bytes, which lies in the same bits but for the low ones the unit
||| leaves 0. Encoding, decoding, the rendering of `LoadPart` and the seed's
||| `idris_apply` all read it here. A kind's parts do not overlap.
public export
place : {0 k : Kind} -> HeaderPart k -> (Bits64, Bits64)
place ConIdP = HeapObj.Shape.place {s = HeapObj.Shape.VALUES} HeapObj.Shape.Part
place ConArityP = HeapObj.Shape.place HeapObj.Shape.Values
place ClosureArityP = HeapObj.Shape.place {s = HeapObj.Shape.MIXED} HeapObj.Shape.Part
place ClosureFilledP = HeapObj.Shape.place HeapObj.Shape.MixedValues
place StringAsciiP = HeapObj.Shape.place {s = HeapObj.Shape.RAW} HeapObj.Shape.Part
place StringBytesP = HeapObj.Shape.place HeapObj.Shape.Bytes
-- four bytes a character: the bytes' bits but for the low two
place StringCharsP =
  (fst (HeapObj.Shape.place HeapObj.Shape.Bytes) + 2,
   snd (HeapObj.Shape.place HeapObj.Shape.Bytes) - 2)
place BignumNegativeP = HeapObj.Shape.place {s = HeapObj.Shape.RAW} HeapObj.Shape.Part
-- eight bytes a limb: the bytes' bits but for the low three
place BignumWordsP =
  (fst (HeapObj.Shape.place HeapObj.Shape.Bytes) + 3,
   snd (HeapObj.Shape.place HeapObj.Shape.Bytes) - 3)
place ArrayElemsP = HeapObj.Shape.place HeapObj.Shape.Values
place StructRawsP = HeapObj.Shape.place HeapObj.Shape.Raws
place StructValuesP = HeapObj.Shape.place HeapObj.Shape.MixedValues
place BytesLengthP = HeapObj.Shape.place HeapObj.Shape.Bytes

||| The bits every header of the kind has: its code, and the counts of its
||| shape that the kind fixes. A header is this word plus its parts, each
||| where `place` puts it.
public export
fixedWord : Kind -> Bits64
fixedWord k = Kind.code k + fixedCounts k
  where
    fixedCounts : Kind -> Bits64
    fixedCounts Kind.CLOSURE = HeapObj.Shape.fieldBits HeapObj.Shape.Raws 1
    fixedCounts Kind.IOREF = HeapObj.Shape.fieldBits HeapObj.Shape.Values 1
    fixedCounts Kind.INT64 = HeapObj.Shape.fieldBits HeapObj.Shape.Bytes 8
    fixedCounts Kind.DOUBLE = HeapObj.Shape.fieldBits HeapObj.Shape.Bytes 8
    fixedCounts Kind.PTR = HeapObj.Shape.fieldBits HeapObj.Shape.Bytes 8
    fixedCounts _ = 0

||| A part of a header word. Inline, so that at a part written in the code
||| the shift and the mask are constants.
public export %inline
readPart : {0 k : Kind} -> HeaderPart k -> (header : Bits64) -> Bits64
readPart p h =
  prim__and_Bits64 (prim__shr_Bits64 h (fst (place p))) (prim__shl_Bits64 1 (snd (place p)) - 1)

||| A part's value where it lives in a header word: the word to add to the
||| kind's `fixedWord` for it.
export %inline
partBits : {0 k : Kind} -> HeaderPart k -> (value : Bits64) -> Bits64
partBits p v = prim__shl_Bits64 v (fst (place p))

||| A header's parts for an object of the kind `k`, as the runtime makes
||| one: the word they add to the kind's `fixedWord`, and whether each fit
||| its field (`place`), which a part too large for it would not, and would
||| spill into the next. Made only part by part (`noParts`, `withPart`), so
||| a part is of the kind's; an object is made, or its header written, only
||| of parts that all fit (`Support.Obj`).
export
record Parts (0 k : Kind) where
  constructor MkParts
  word : Bits64
  fit : Bool

||| No parts: the header is the kind's `fixedWord`.
export %inline
noParts : Parts k
noParts = MkParts 0 True

||| The parts and one more, the value where `place` puts the part.
export %inline
withPart : {0 k : Kind} -> HeaderPart k -> (value : Bits64) -> Parts k -> Parts k
withPart p v ps =
  MkParts (ps.word + partBits p v) (ps.fit && v < prim__shl_Bits64 1 (snd (place p)))

||| The header word of the parts, the kind's `fixedWord` with them, and
||| whether they all fit.
export %inline
headerWord : (k : Kind) -> Parts k -> Bits64
headerWord k ps = fixedWord k + ps.word

export %inline
allFit : Parts k -> Bool
allFit ps = ps.fit

||| What adding one to a part adds to the header word: a closure with one
||| more argument filled is its header plus `partUnit ClosureFilledP`.
public export
partUnit : {0 k : Kind} -> HeaderPart k -> Integer
partUnit p = prim__shl_Integer 1 (cast (fst (place p)))

||| Whether two headers, of any kinds, are the same header.
public export
sameHeader : {enc : Enc} -> {k, k' : Kind} -> Header enc k -> Header enc k' -> Bool
sameHeader h h' = k == k' && map snd (parts h) == map snd (parts h')

||| Whether every part fits its width. Every header the IR carries comes with
||| the proof (`wellFormed` in `Native.Codegen.TermIR.FieldTys`); encoding a header that does
||| not fit loses the high bits of the part, and never touches its neighbours.
public export
fits : {enc : Enc} -> {0 k : Kind} -> Header enc k -> Bool
fits h = all (\pv => cast (snd pv) < prim__shl_Integer 1 (cast (snd (place (fst pv))))) (parts h)

||| The header word, with flags 0.
export
encodeHeader : {enc : Enc} -> {k : Kind} -> Header enc k -> Int64
encodeHeader h = signed (cast (fixedWord k) + sum (map part (parts h)))
  where
    part : (HeaderPart k, Nat) -> Integer
    part (p, v) = (cast v `mod` prim__shl_Integer 1 (cast (snd (place p))))
      * prim__shl_Integer 1 (cast (fst (place p)))

    signed : Integer -> Int64
    signed u = cast (if u >= prim__shl_Integer 1 63 then u - prim__shl_Integer 1 64 else u)

||| The header a word encodes, if the word is exactly what `encodeHeader`
||| makes of some header: a kind's code other than `CONT`'s, flags 0, the
||| counts the kind fixes, and no bit outside the kind's parts. So
||| `decodeHeader w = Just (k ** h)` implies `encodeHeader h = w`, and for a
||| header that fits, `decodeHeader (encodeHeader h)` gives the header back,
||| which `tests/native/header001` checks for every part at its boundaries.
export
decodeHeader : (enc : Enc) -> Int64 -> Maybe (k : Kind ** Header enc k)
decodeHeader enc w = do
  r <- parse (Kind.fromCode (cast (u `mod` 65536)))
  if encodeHeader (snd r) == w then Just r else Nothing
  where
    unsigned : Int64 -> Integer
    unsigned w = if w < 0 then cast w + prim__shl_Integer 1 64 else cast w

    u : Integer
    u = unsigned w

    get : HeaderPart k -> Nat
    get p =
      cast
        ((u `div` prim__shl_Integer 1 (cast (fst (place p)))) `mod` prim__shl_Integer 1
         (cast (snd (place p))))

    -- A sign-magnitude program's BIGNUM header, matched on the record so
    -- that the match gives the parts' type.
    bignum : (enc' : Enc) -> Maybe (k : Kind ** Header enc' k)
    bignum (MkEnc _ (MkBignumEnc _ BignumEnc.SignMagnitude) _) =
      Just
        (Kind.BIGNUM **
         BignumH (BignumEnc.MkSignMagnitudeParts (get BignumNegativeP == 1) (get BignumWordsP)))
    bignum _ = Nothing

    -- A string's header, matched on the record so that the match gives the
    -- parts' type.
    string : (enc' : Enc) -> Maybe (k : Kind ** Header enc' k)
    string (MkEnc _ _ StringEnc.Utf8) =
      Just
        (Kind.STRING ** StringH (StringEnc.MkUtf8Parts (get StringAsciiP == 1) (get StringBytesP)))
    string (MkEnc _ _ StringEnc.Utf32) =
      Just (Kind.STRING ** StringH (StringEnc.MkUtf32Parts (get StringCharsP)))

    parse : Maybe Kind -> Maybe (k : Kind ** Header enc k)
    parse (Just Kind.CON) = Just (Kind.CON ** ConH (get ConIdP) (get ConArityP))
    parse (Just Kind.CLOSURE) =
      Just (Kind.CLOSURE ** ClosureH (get ClosureArityP) (get ClosureFilledP))
    parse (Just Kind.INT64) = Just (Kind.INT64 ** Int64H)
    parse (Just Kind.DOUBLE) = Just (Kind.DOUBLE ** DoubleH)
    parse (Just Kind.STRING) = string enc
    parse (Just Kind.BIGNUM) = bignum enc
    parse (Just Kind.IOREF) = Just (Kind.IOREF ** IORefH)
    parse (Just Kind.ARRAY) = Just (Kind.ARRAY ** ArrayH (get ArrayElemsP))
    parse (Just Kind.STRUCT) = Just (Kind.STRUCT ** StructH (get StructRawsP) (get StructValuesP))
    parse (Just Kind.BYTES) = Just (Kind.BYTES ** BytesH (get BytesLengthP))
    parse (Just Kind.PTR) = Just (Kind.PTR ** PtrH)
    parse (Just Kind.CONT) = Nothing
    parse Nothing = Nothing

||| The header's counts, of its kind's shape (`Kind.shape`), which its type
||| says: a header's counts of another shape do not typecheck.
public export
counts : {enc : Enc} -> {0 k : Kind} -> (h : Header enc k) ->
         HeapObj.Shape.Counts (Kind.headedShape k @{headed h})
counts (ConH _ a) = HeapObj.Shape.ValuesOf a
counts (ClosureH _ f) = HeapObj.Shape.MixedOf 1 f
counts Int64H = HeapObj.Shape.WordsOf 1
counts DoubleH = HeapObj.Shape.WordsOf 1
counts (StringH p) = strings enc.string p
  where
    strings : (s : StringEnc) -> StringEnc.StringParts s -> HeapObj.Shape.Counts HeapObj.Shape.RAW
    strings StringEnc.Utf8 q = HeapObj.Shape.BytesOf q.bytes
    strings StringEnc.Utf32 q = HeapObj.Shape.BytesOf (4 * q.chars)
counts (BignumH p) = bignums enc.bignum p
  where
    bignums : (b : BignumEnc) -> BignumEnc.BignumParts b -> HeapObj.Shape.Counts HeapObj.Shape.RAW
    bignums (MkBignumEnc _ BignumEnc.SignMagnitude) q = HeapObj.Shape.WordsOf q.words
    bignums (MkBignumEnc _ BignumEnc.TwosComplement) q = absurd q
counts IORefH = HeapObj.Shape.ValuesOf 1
counts (ArrayH n) = HeapObj.Shape.ValuesOf n
counts (StructH r v) = HeapObj.Shape.MixedOf r v
counts (BytesH n) = HeapObj.Shape.BytesOf n
counts PtrH = HeapObj.Shape.WordsOf 1

||| The number of fields: the object's words after its header.
public export
fieldWords : {enc : Enc} -> {0 k : Kind} -> Header enc k -> Nat
fieldWords h = HeapObj.Shape.fieldWords (counts h)

||| The object's size in words, its header included.
public export
objectWords : {enc : Enc} -> {0 k : Kind} -> Header enc k -> Nat
objectWords h = 1 + fieldWords h

||| The collector's view: the word, counting the header as word 0, where the
||| scanned fields begin, and how many there are. Every other field is raw.
public export
scanned : {enc : Enc} -> {0 k : Kind} -> Header enc k -> (Nat, Nat)
scanned h = HeapObj.Shape.scanned (counts h)
