||| What an object is in memory: its header (`Header`), and the sizes and
||| scanned fields the header gives.
|||
||| Every heap object is 8-byte aligned and begins with one header word, which
||| says what the object is: its kind (`Compiler.Native.HeapObject.Kind`), and
||| the parts of its header, whose number and meaning depend on the kind. The
||| words after the header are the object's fields; offsets below are in bytes
||| from the start of the object. The header alone gives the object's size and
||| which of its fields the collector scans (`objectWords`, `scanned`); the
||| collector needs nothing else. The exception is `CONT`, which has no header
||| word.
|||
||| The header word: the kind's id in bits 0..3; flags in bits 4..7, which the
||| compiler always leaves 0 (the collector uses bit 4 as the mark bit of the
||| large space during a full collection); from bit 8, the header's parts,
||| laid out per kind (`place`).
|||
||| Static objects (`Compiler.Native.LocatedIR.Static`) have exactly the
||| same layouts.
|||
||| Part of the heap-object model, the contract between compiled code and the
||| runtime (`Compiler.Native.HeapObject.Enc` says what it is): it imports
||| nothing from the compiler, so that the runtime's own Idris can import it.
module Compiler.Native.HeapObject.Header

import Compiler.Native.HeapObject.BignumEnc
import Compiler.Native.HeapObject.Enc
import Compiler.Native.HeapObject.Kind
import Compiler.Native.HeapObject.StringEnc

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
partUnit p = prim__shl_Integer 1 (cast (fst (place p)))

||| Whether two headers, of any kinds, are the same header.
public export
sameHeader : {k, k' : Kind} -> Header enc k -> Header enc k' -> Bool
sameHeader h h' = k == k' && map snd (parts h) == map snd (parts h')

||| Whether every part fits its width. Every header the IR carries comes with
||| the proof (`wellFormed` in `Compiler.Native.TermIR.FieldTys`); encoding a header that does
||| not fit loses the high bits of the part, and never touches its neighbours.
public export
fits : {0 k : Kind} -> Header enc k -> Bool
fits h = all (\pv => cast (snd pv) < prim__shl_Integer 1 (cast (snd (place (fst pv))))) (parts h)

||| The header word, with flags 0.
export
encodeHeader : {k : Kind} -> Header enc k -> Int64
encodeHeader h = signed (cast (Kind.kindId k) + sum (map part (parts h)))
  where
    part : (HeaderPart k', Nat) -> Integer
    part (p, v) = (cast v `mod` prim__shl_Integer 1 (cast (snd (place p)))) * prim__shl_Integer 1 (cast (fst (place p)))

    signed : Integer -> Int64
    signed u = cast (if u >= prim__shl_Integer 1 63 then u - prim__shl_Integer 1 64 else u)

||| The header a word encodes, if the word is exactly what `encodeHeader`
||| makes of some header: a kind's id other than `CONT`'s, flags 0, and no
||| bit outside the kind's parts. So `decodeHeader w = Just (k ** h)` implies
||| `encodeHeader h = w`, and for a header that fits,
||| `decodeHeader (encodeHeader h)` gives the header back, which
||| `tests/native/header001` checks for every part at its boundaries.
export
decodeHeader : (enc : Enc) -> Int64 -> Maybe (k : Kind ** Header enc k)
decodeHeader enc w = do
  r <- parse (Kind.kindOfId (cast (u `mod` 16)))
  if encodeHeader (snd r) == w then Just r else Nothing
  where
    unsigned : Int64 -> Integer
    unsigned w = if w < 0 then cast w + prim__shl_Integer 1 64 else cast w

    u : Integer
    u = unsigned w

    get : HeaderPart k' -> Nat
    get p = cast ((u `div` prim__shl_Integer 1 (cast (fst (place p)))) `mod` prim__shl_Integer 1 (cast (snd (place p))))

    -- A sign-magnitude program's BIGNUM header, matched on the record so
    -- that the match proves the sign is in the header.
    bignum : (enc' : Enc) -> Maybe (k : Kind ** Header enc' k)
    bignum (Enc.MkEnc _ (BignumEnc.MkBignumEnc _ BignumEnc.SignMagnitude) _) =
      Just (Kind.BIGNUM ** BignumH (get BignumNegative == 1) (get BignumWords))
    bignum _ = Nothing

    -- A string's header, matched on the record so that the match proves the
    -- encoding the constructor needs.
    string : (enc' : Enc) -> Maybe (k : Kind ** Header enc' k)
    string (Enc.MkEnc _ _ StringEnc.Utf8) = Just (Kind.STRING ** StringH (get StringAscii == 1) (get StringBytes))
    string (Enc.MkEnc _ _ StringEnc.Utf32) = Just (Kind.STRING ** StringCharsH (get StringChars))

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

||| The number of fields: the object's words after its header.
public export
fieldWords : {0 k : Kind} -> Header enc k -> Nat
fieldWords h = case h of
  ConH _ a => a
  ClosureH _ f => 1 + f
  Int64H => 1
  DoubleH => 1
  StringH _ n => byteWords n
  StringCharsH n => byteWords (4 * n)
  BignumH _ n => n
  IORefH => 1
  ArrayH n => n
  BufferH n => byteWords n
  PtrH => 1
  where
    -- the words a payload of so many bytes fills, padded to whole words
    byteWords : Nat -> Nat
    byteWords n = cast ((the Integer (cast n) + 7) `div` 8)

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
