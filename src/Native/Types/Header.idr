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

import Native.HeapObj.Shape as HeapObj

%default total

||| What a header says, per kind and under the program's encodings: one
||| constructor for each kind that has a header, whose arguments are the
||| header's parts, named for their meaning. No constructor makes a
||| `Header enc CONT`, since a continuation has no header. A `BIGNUM`'s header
||| depends on its bignum encoding; only the sign-magnitude one exists so far.
public export
data Header : Enc -> Kind -> Type where
  ConH     : (conId : Nat) -> (arity : Nat) -> Header enc Kind.CON
  ClosureH : (arity : Nat) -> (filled : Nat) -> Header enc Kind.CLOSURE
  Int64H   : Header enc Kind.INT64
  DoubleH  : Header enc Kind.DOUBLE
  StringH  : {auto 0 u : StringEnc.Utf8Strings enc.string} -> (ascii : Bool) -> (bytes : Nat) -> Header enc Kind.STRING
  StringCharsH : {auto 0 u : StringEnc.Utf32Strings enc.string} -> (chars : Nat) -> Header enc Kind.STRING
  BignumH  : {auto 0 sh : BignumEnc.SignInHeader enc.bignum} -> (negative : Bool) -> (words : Nat) ->
             Header enc Kind.BIGNUM
  IORefH   : Header enc Kind.IOREF
  ArrayH   : (elems : Nat) -> Header enc Kind.ARRAY
  BufferH  : (bytes : Nat) -> Header enc Kind.BUFFER
  PtrH     : Header enc Kind.PTR

||| A continuation has no header.
public export
Uninhabited (Header enc Kind.CONT) where
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

||| A part of a header, by kind: what `LoadPart` reads.
public export
data HeaderPart : Kind -> Type where
  ConId          : HeaderPart Kind.CON
  ConArity       : HeaderPart Kind.CON
  ClosureArity   : HeaderPart Kind.CLOSURE
  ClosureFilled  : HeaderPart Kind.CLOSURE
  StringAscii    : HeaderPart Kind.STRING
  StringBytes    : HeaderPart Kind.STRING
  StringChars    : HeaderPart Kind.STRING
  BignumNegative : HeaderPart Kind.BIGNUM
  BignumWords    : HeaderPart Kind.BIGNUM
  ArrayElems     : HeaderPart Kind.ARRAY
  BufferBytes    : HeaderPart Kind.BUFFER

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

||| Where a part lives in the header word: its first bit and its width, as
||| the words the runtime's code shifts and masks by: a field of the kind's
||| shape (`Shape.place`), or a count of whole units of a shape's count of
||| bytes, which lies in the same bits but for the low ones the unit
||| leaves 0. Encoding, decoding, the rendering of `LoadPart` and the seed's
||| `idris_apply` all read it here. A kind's parts do not overlap.
public export
place : {0 k : Kind} -> HeaderPart k -> (Bits64, Bits64)
place ConId = HeapObj.Shape.place {s = HeapObj.Shape.VALUES} HeapObj.Shape.Part
place ConArity = HeapObj.Shape.place HeapObj.Shape.Values
place ClosureArity = HeapObj.Shape.place {s = HeapObj.Shape.MIXED} HeapObj.Shape.Part
place ClosureFilled = HeapObj.Shape.place HeapObj.Shape.MixedValues
place StringAscii = HeapObj.Shape.place {s = HeapObj.Shape.RAW} HeapObj.Shape.Part
place StringBytes = HeapObj.Shape.place HeapObj.Shape.Bytes
-- four bytes a character: the bytes' bits but for the low two
place StringChars = (fst (HeapObj.Shape.place HeapObj.Shape.Bytes) + 2, snd (HeapObj.Shape.place HeapObj.Shape.Bytes) - 2)
place BignumNegative = HeapObj.Shape.place {s = HeapObj.Shape.RAW} HeapObj.Shape.Part
-- eight bytes a limb: the bytes' bits but for the low three
place BignumWords = (fst (HeapObj.Shape.place HeapObj.Shape.Bytes) + 3, snd (HeapObj.Shape.place HeapObj.Shape.Bytes) - 3)
place ArrayElems = HeapObj.Shape.place HeapObj.Shape.Values
place BufferBytes = HeapObj.Shape.place HeapObj.Shape.Bytes

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
readPart p h = prim__and_Bits64 (prim__shr_Bits64 h (fst (place p))) (prim__shl_Bits64 1 (snd (place p)) - 1)

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
||| more argument filled is its header plus `partUnit ClosureFilled`.
public export
partUnit : {0 k : Kind} -> HeaderPart k -> Integer
partUnit p = prim__shl_Integer 1 (cast (fst (place p)))

||| Whether two headers, of any kinds, are the same header.
public export
sameHeader : {k, k' : Kind} -> Header enc k -> Header enc k' -> Bool
sameHeader h h' = k == k' && map snd (parts h) == map snd (parts h')

||| Whether every part fits its width. Every header the IR carries comes with
||| the proof (`wellFormed` in `Native.Codegen.TermIR.FieldTys`); encoding a header that does
||| not fit loses the high bits of the part, and never touches its neighbours.
public export
fits : {0 k : Kind} -> Header enc k -> Bool
fits h = all (\pv => cast (snd pv) < prim__shl_Integer 1 (cast (snd (place (fst pv))))) (parts h)

||| The header word, with flags 0.
export
encodeHeader : {k : Kind} -> Header enc k -> Int64
encodeHeader h = signed (cast (fixedWord k) + sum (map part (parts h)))
  where
    part : (HeaderPart k, Nat) -> Integer
    part (p, v) = (cast v `mod` prim__shl_Integer 1 (cast (snd (place p)))) * prim__shl_Integer 1 (cast (fst (place p)))

    signed : Integer -> Int64
    signed u = cast (if u >= prim__shl_Integer 1 63 then u - prim__shl_Integer 1 64 else u)

||| The header a word encodes, if the word is exactly what `encodeHeader`
||| makes of some header: a kind's code other than `CONT`'s, flags 0, the
||| counts the kind fixes, and no bit outside the kind's parts. So `decodeHeader w = Just (k ** h)` implies
||| `encodeHeader h = w`, and for a header that fits,
||| `decodeHeader (encodeHeader h)` gives the header back, which
||| `tests/native/header001` checks for every part at its boundaries.
export
decodeHeader : (enc : Enc) -> Int64 -> Maybe (k : Kind ** Header enc k)
decodeHeader enc w = do
  r <- parse (Kind.kindOfCode (cast (u `mod` 65536)))
  if encodeHeader (snd r) == w then Just r else Nothing
  where
    unsigned : Int64 -> Integer
    unsigned w = if w < 0 then cast w + prim__shl_Integer 1 64 else cast w

    u : Integer
    u = unsigned w

    get : HeaderPart k -> Nat
    get p = cast ((u `div` prim__shl_Integer 1 (cast (fst (place p)))) `mod` prim__shl_Integer 1 (cast (snd (place p))))

    -- A sign-magnitude program's BIGNUM header, matched on the record so
    -- that the match proves the sign is in the header.
    bignum : (enc' : Enc) -> Maybe (k : Kind ** Header enc' k)
    bignum (MkEnc _ (MkBignumEnc _ BignumEnc.SignMagnitude) _) =
      Just (Kind.BIGNUM ** BignumH (get BignumNegative == 1) (get BignumWords))
    bignum _ = Nothing

    -- A string's header, matched on the record so that the match proves the
    -- encoding the constructor needs.
    string : (enc' : Enc) -> Maybe (k : Kind ** Header enc' k)
    string (MkEnc _ _ StringEnc.Utf8) = Just (Kind.STRING ** StringH (get StringAscii == 1) (get StringBytes))
    string (MkEnc _ _ StringEnc.Utf32) = Just (Kind.STRING ** StringCharsH (get StringChars))

    parse : Maybe Kind -> Maybe (k : Kind ** Header enc k)
    parse (Just Kind.CON) = Just (Kind.CON ** ConH (get ConId) (get ConArity))
    parse (Just Kind.CLOSURE) = Just (Kind.CLOSURE ** ClosureH (get ClosureArity) (get ClosureFilled))
    parse (Just Kind.INT64) = Just (Kind.INT64 ** Int64H)
    parse (Just Kind.DOUBLE) = Just (Kind.DOUBLE ** DoubleH)
    parse (Just Kind.STRING) = string enc
    parse (Just Kind.BIGNUM) = bignum enc
    parse (Just Kind.IOREF) = Just (Kind.IOREF ** IORefH)
    parse (Just Kind.ARRAY) = Just (Kind.ARRAY ** ArrayH (get ArrayElems))
    parse (Just Kind.BUFFER) = Just (Kind.BUFFER ** BufferH (get BufferBytes))
    parse (Just Kind.PTR) = Just (Kind.PTR ** PtrH)
    parse (Just Kind.CONT) = Nothing
    parse Nothing = Nothing

||| The header's counts, by its kind's shape.
public export
counts : {0 k : Kind} -> Header enc k -> (s : HeapObj.Shape ** HeapObj.Shape.Counts s)
counts h = case h of
  ConH _ a => (_ ** HeapObj.Shape.ValuesOf a)
  ClosureH _ f => (_ ** HeapObj.Shape.MixedOf 1 f)
  Int64H => (_ ** HeapObj.Shape.WordsOf 1)
  DoubleH => (_ ** HeapObj.Shape.WordsOf 1)
  StringH _ n => (_ ** HeapObj.Shape.BytesOf n)
  StringCharsH n => (_ ** HeapObj.Shape.BytesOf (4 * n))
  BignumH _ n => (_ ** HeapObj.Shape.WordsOf n)
  IORefH => (_ ** HeapObj.Shape.ValuesOf 1)
  ArrayH n => (_ ** HeapObj.Shape.ValuesOf n)
  BufferH n => (_ ** HeapObj.Shape.BytesOf n)
  PtrH => (_ ** HeapObj.Shape.WordsOf 1)

||| The number of fields: the object's words after its header.
public export
fieldWords : {0 k : Kind} -> Header enc k -> Nat
fieldWords h = HeapObj.Shape.fieldWords (snd (counts h))

||| The object's size in words, its header included.
public export
objectWords : {0 k : Kind} -> Header enc k -> Nat
objectWords h = 1 + fieldWords h

||| The collector's view: the word, counting the header as word 0, where the
||| scanned fields begin, and how many there are. Every other field is raw.
public export
scanned : {0 k : Kind} -> Header enc k -> (Nat, Nat)
scanned h = HeapObj.Shape.scanned (snd (counts h))
