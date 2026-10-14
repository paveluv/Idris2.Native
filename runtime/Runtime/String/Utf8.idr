||| Strings under UTF-8: the one module of the runtime that reads a string's
||| header or bytes. Every other part of the runtime, and generated code,
||| reaches a string through these functions, which the native code
||| generator binds when a program's strings are UTF-8.
|||
||| A `STRING` is a header word, then its bytes from offset 8, padded with
||| zeros to a word. The header holds the kind, the byte count, and the ASCII
||| bit, set exactly when every byte is below 0x80. The bytes are always a
||| well-formed UTF-8 encoding of Unicode scalar values, shortest form: every
||| function that makes a string keeps it, and every one that reads a string
||| relies on it, a decoder trusting a lead byte's length.
|||
||| Idris counts strings in characters. Under the ASCII bit a character is a
||| byte, and every operation is a byte operation; without it, finding a
||| character scans from the start. A function that makes a string knows its
||| ASCII bit without another pass: the AND of its inputs' bits, inherited by
||| a part of an ASCII string, or seen in the bytes it copies anyway.
|||
||| The semantics are Chez's, which Idris's Chez backend gives the
||| primitives, wherever Chez defines them: `substr` clamps its start and its
||| length to the string. Outside the string, `head`, `tail` and `index` end
||| the program. Chez ends it only for `tail`: its programs are compiled
||| without bounds checks, so its `head` and `index` there read past the
||| string.
module Runtime.String.Utf8

import Compiler.Native.HeapObject.Header
import Compiler.Native.HeapObject.Kind
import Flat.Uniform
import Runtime.Bits
import Runtime.Heap
import Runtime.Memory
import Runtime.Object
import Runtime.Space

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

------------------------------------------------------------------------------
-- The layout

||| The bytes a header counts, and whether it says they are all ASCII.
bytesOf : (header : Bits64) -> Bits64
bytesOf = part StringBytes

asciiOf : (header : Bits64) -> Bool
asciiOf h = part StringAscii h == 1

||| The header of a string of `bytes`.
headerFor : (ascii : Bool) -> (bytes : Bits64) -> Bits64
headerFor ascii bytes =
  kindId STRING + shiftL (if ascii then 1 else 0) (fst (place StringAscii)) + shiftL bytes (fst (place StringBytes))

||| A string's header.
headerOf : Addr STRING -> Op Heap Bits64
headerOf s = load64 s 0

||| A new string of `bytes`, its header saying it is ASCII until `finish`
||| sets it, its bytes still to be written, its padding zero.
newString : (bytes : Bits64) -> Op Heap (Addr STRING)
newString bytes = do
  let words = byteWords bytes
  a <- allocate (8 * (1 + words))
  let s = fromWord {k = STRING} a
  store64 s 0 (headerFor True bytes)
  if words == 0 then pure s else do
    store64 s (8 * words) 0
    pure s

||| A new string's header set, and the string as ordinary code holds it.
finish : Addr STRING -> (ascii : Bool) -> (bytes : Bits64) -> Op Heap (Uniform String)
finish s ascii bytes = do
  store64 s 0 (headerFor ascii bytes)
  stringValue s

||| The byte at `i`, and storing one.
byteAt : Addr STRING -> (i : Bits64) -> Op Heap Bits64
byteAt s i = load8 s (8 + i)

setByte : Addr STRING -> (i, b : Bits64) -> Op Heap ()
setByte s i b = store8 s (8 + i) b

------------------------------------------------------------------------------
-- UTF-8

||| The bytes of the character whose lead byte is `b`.
seqLength : (lead : Bits64) -> Bits64
seqLength b = if b < 0x80 then 1 else if b < 0xE0 then 2 else if b < 0xF0 then 3 else 4

||| The bytes of the character `c`, shortest form.
charBytes : (c : Bits64) -> Bits64
charBytes c = if c < 0x80 then 1 else if c < 0x800 then 2 else if c < 0x10000 then 3 else 4

||| The character whose lead byte is at `i`.
decodeAt : Addr STRING -> (i : Bits64) -> Op Heap Bits64
decodeAt s i = do
  b0 <- byteAt s i
  if b0 < 0x80 then pure b0 else
    if b0 < 0xE0 then do
      b1 <- byteAt s (i + 1)
      pure (shiftL (b0 .&. 0x1F) 6 .|. b1 .&. 0x3F)
    else if b0 < 0xF0 then do
      b1 <- byteAt s (i + 1)
      b2 <- byteAt s (i + 2)
      pure (shiftL (b0 .&. 0x0F) 12 .|. shiftL (b1 .&. 0x3F) 6 .|. b2 .&. 0x3F)
    else do
      b1 <- byteAt s (i + 1)
      b2 <- byteAt s (i + 2)
      b3 <- byteAt s (i + 3)
      pure (shiftL (b0 .&. 0x07) 18 .|. shiftL (b1 .&. 0x3F) 12
            .|. shiftL (b2 .&. 0x3F) 6 .|. b3 .&. 0x3F)

||| The character `c` written at `j`, its `charBytes c` bytes.
encodeAt : Addr STRING -> (j, c : Bits64) -> Op Heap ()
encodeAt s j c =
  if c < 0x80 then setByte s j c
  else if c < 0x800 then do
    setByte s j (0xC0 .|. shiftR c 6)
    setByte s (j + 1) (0x80 .|. c .&. 0x3F)
  else if c < 0x10000 then do
    setByte s j (0xE0 .|. shiftR c 12)
    setByte s (j + 1) (0x80 .|. shiftR c 6 .&. 0x3F)
    setByte s (j + 2) (0x80 .|. c .&. 0x3F)
  else do
    setByte s j (0xF0 .|. shiftR c 18)
    setByte s (j + 1) (0x80 .|. shiftR c 12 .&. 0x3F)
    setByte s (j + 2) (0x80 .|. shiftR c 6 .&. 0x3F)
    setByte s (j + 3) (0x80 .|. c .&. 0x3F)

------------------------------------------------------------------------------
-- Loops

||| The characters from byte `i` to `end`: the bytes that are not a
||| continuation byte, `10xxxxxx`. Ends: `i` climbs to `end`.
covering
countChars : Addr STRING -> (i, end, count : Bits64) -> Op Heap Bits64
countChars s i end count =
  if i >= end then pure count else do
    b <- byteAt s i
    countChars s (i + 1) end (if b .&. 0xC0 == 0x80 then count else count + 1)

||| The byte offset of the `n`th character of a string of the header.
covering
offsetOf : Addr STRING -> (header, n : Bits64) -> Op Heap Bits64
offsetOf s h n =
  if asciiOf h then pure (if n > bytesOf h then bytesOf h else n)
  else skipChars s 0 (bytesOf h) n
  where
    ||| The byte offset `n` characters after `i`, or `end` if there are fewer.
    ||| Ends: `n` falls to 0, or `i` climbs to `end`.
    covering
    skipChars : Addr STRING -> (i, end, n : Bits64) -> Op Heap Bits64
    skipChars s i end n =
      if n == 0 || i >= end then pure (if i > end then end else i) else do
        b <- byteAt s i
        skipChars s (i + seqLength b) end (n - 1)

||| Copy `n` bytes from `i` in one string to `j` in another; the OR of the
||| bytes, whose top bit says whether any is not ASCII. Ends: `n` falls to 0.
covering
copyBytes : (from : Addr STRING) -> (i : Bits64) -> (to : Addr STRING) -> (j, n, seen : Bits64) -> Op Heap Bits64
copyBytes from i to j n seen =
  if n == 0 then pure seen else do
    b <- byteAt from i
    setByte to j b
    copyBytes from (i + 1) to (j + 1) (n - 1) (seen .|. b)

||| The bytes from `from` to `to` of a string, as a new string: ASCII if the
||| string is, or if the bytes copied are.
covering
slice : Addr STRING -> (header, from, to : Bits64) -> Op Heap (Uniform String)
slice s h from to = do
  let n = to - from
  r <- newString n
  seen <- copyBytes s from r 0 n 0
  finish r (asciiOf h || seen < 0x80) n

------------------------------------------------------------------------------
-- The primitives

%cg native flat Runtime.String.Utf8.length
||| The characters of a string.
export covering
length : Uniform String -> Op Heap Bits64
length str = do
  s <- stringObject str
  h <- headerOf s
  if asciiOf h then pure (bytesOf h) else countChars s 0 (bytesOf h) 0

%cg native flat Runtime.String.Utf8.head
||| The first character.
export
head : Uniform String -> Op Heap Bits64
head str = do
  s <- stringObject str
  h <- headerOf s
  if bytesOf h == 0 then crashOp "idris: the head of an empty string" else decodeAt s 0

%cg native flat Runtime.String.Utf8.tail
||| All but the first character.
export covering
tail : Uniform String -> Op Heap (Uniform String)
tail str = do
  s <- stringObject str
  h <- headerOf s
  if bytesOf h == 0 then crashOp "idris: the tail of an empty string" else do
    b <- byteAt s 0
    slice s h (seqLength b) (bytesOf h)

%cg native flat Runtime.String.Utf8.index
||| The character at an index. A negative index comes as a word past every
||| length.
export covering
index : Uniform String -> (i : Bits64) -> Op Heap Bits64
index str i = do
  s <- stringObject str
  h <- headerOf s
  off <- offsetOf s h i
  if off >= bytesOf h then crashOp "idris: an index outside a string" else decodeAt s off

%cg native flat Runtime.String.Utf8.cons
||| A character, then a string.
export covering
cons : (c : Bits64) -> Uniform String -> Op Heap (Uniform String)
cons c str = do
  s <- stringObject str
  h <- headerOf s
  let k = charBytes c
  let n = bytesOf h
  r <- newString (k + n)
  encodeAt r 0 c
  _ <- copyBytes s 0 r k n 0
  finish r (c < 0x80 && asciiOf h) (k + n)

%cg native flat Runtime.String.Utf8.append
||| One string, then another.
export covering
append : Uniform String -> Uniform String -> Op Heap (Uniform String)
append x y = do
  a <- stringObject x
  b <- stringObject y
  ha <- headerOf a
  hb <- headerOf b
  let na = bytesOf ha
  let nb = bytesOf hb
  r <- newString (na + nb)
  _ <- copyBytes a 0 r 0 na 0
  _ <- copyBytes b 0 r na nb 0
  finish r (asciiOf ha && asciiOf hb) (na + nb)

%cg native flat Runtime.String.Utf8.reverse
||| The characters in the other order.
export covering
reverse : Uniform String -> Op Heap (Uniform String)
reverse str = do
  s <- stringObject str
  h <- headerOf s
  let n = bytesOf h
  r <- newString n
  reverseFrom s 0 n r
  finish r (asciiOf h) n
  where
    ||| The characters of a string from byte `i` to `n`, each written at the
    ||| mirror of its place in `r`. Ends: `i` climbs to `n`.
    covering
    reverseFrom : Addr STRING -> (i, n : Bits64) -> Addr STRING -> Op Heap ()
    reverseFrom s i n r =
      if i >= n then pure () else do
        b <- byteAt s i
        let k = seqLength b
        _ <- copyBytes s i r (n - i - k) k 0
        reverseFrom s (i + k) n r

%cg native flat Runtime.String.Utf8.substr
||| `len` characters from `start`, both clamped to the string, as Chez's
||| `string-substr` does: a negative one counts as 0, and a start past the
||| end gives the empty string.
export covering
substr : (start, len : Int) -> Uniform String -> Op Heap (Uniform String)
substr start len str = do
  s <- stringObject str
  h <- headerOf s
  let n = bytesOf h
  count <- if asciiOf h then pure n else countChars s 0 n 0
  let b = if start < 0 then 0 else cast {to = Bits64} start
  let x = if len < 0 then 0 else cast {to = Bits64} len
  let e = if x > count - b then count else b + x
  if b > count then slice s h 0 0 else do
    from <- offsetOf s h b
    to <- offsetOf s h e
    slice s h from to

%cg native flat Runtime.String.Utf8.compare
||| The order of two strings, -1, 0 or 1: by code point, which is the order
||| of their UTF-8 bytes.
export covering
compare : Uniform String -> Uniform String -> Op Heap Int
compare x y = do
  a <- stringObject x
  b <- stringObject y
  ha <- headerOf a
  hb <- headerOf b
  compareFrom a b 0 (bytesOf ha) (bytesOf hb)
  where
    ||| Compare two strings' bytes from `i`: the first difference, else the
    ||| shorter first. Ends: `i` climbs to the shorter's length.
    covering
    compareFrom : Addr STRING -> Addr STRING -> (i, na, nb : Bits64) -> Op Heap Int
    compareFrom a b i na nb =
      if i >= na || i >= nb then pure (if na < nb then -1 else if na > nb then 1 else 0) else do
        p <- byteAt a i
        q <- byteAt b i
        if p < q then pure (-1) else if p > q then pure 1 else compareFrom a b (i + 1) na nb

------------------------------------------------------------------------------
-- Lists of characters and of strings: `prelude`'s `fastPack`, `fastUnpack`
-- and `fastConcat`. A list is a `CON` object: `[]` of constructor id 0 and
-- no fields, often the static one; `(::)` of id 1, its head then its tail.
-- A character in a field is its fixnum, a string or a list a pointer.

||| Whether a list's cell is `[]`.
isNil : Addr CON -> Op Heap Bool
isNil cell = do
  h <- load64 cell 0
  pure (part ConId h == 0)

%cg native flat Runtime.String.Utf8.fastPack
||| `fastPack`: a list of characters as a string.
export covering
fastPack : Uniform (List Char) -> Uniform String
fastPack xs = let (MkHeap # r) = packOp xs MkHeap in r
  where
    ||| A list of characters as a string.
    covering
    packOp : Uniform (List Char) -> Op Heap (Uniform String)
    packOp xs = do
      cell <- conObject xs
      (n, seen) <- packMeasure cell 0 0
      s <- newString n
      packWrite cell s 0
      finish s (seen < 0x80) n
      where
        ||| The bytes the characters of a list take, and the OR of their code
        ||| points. Ends: the list is finite, each step one cell on.
        covering
        packMeasure : Addr CON -> (bytes, seen : Bits64) -> Op Heap (Bits64, Bits64)
        packMeasure cell bytes seen = do
          end <- isNil cell
          if end then pure (bytes, seen) else do
            c <- load64 cell 8
            t <- load64 cell 16
            next <- fieldObject {k = CON} t
            let ch = fixnumOf c
            packMeasure next (bytes + charBytes ch) (seen .|. ch)

        ||| The characters of a list written from `j`. Ends: as `packMeasure`.
        covering
        packWrite : Addr CON -> Addr STRING -> (j : Bits64) -> Op Heap ()
        packWrite cell s j = do
          end <- isNil cell
          if end then pure () else do
            c <- load64 cell 8
            t <- load64 cell 16
            next <- fieldObject {k = CON} t
            let ch = fixnumOf c
            encodeAt s j ch
            packWrite next s (j + charBytes ch)

%cg native flat Runtime.String.Utf8.fastUnpack
||| `fastUnpack`: a string as a list of characters.
export covering
fastUnpack : Uniform String -> Uniform (List Char)
fastUnpack str = let (MkHeap # r) = unpackOp str MkHeap in r
  where
    ||| A string as a list of characters.
    covering
    unpackOp : Uniform String -> Op Heap (Uniform (List Char))
    unpackOp str = do
      s <- stringObject str
      h <- headerOf s
      n <- if asciiOf h then pure (bytesOf h) else countChars s 0 (bytesOf h) 0
      block <- allocate (8 + 24 * n)
      store64 (fromWord {k = CON} block) 0 nilHeader
      unpackFill s 0 0 n block
      conValue (fromWord (if n == 0 then block else block + 8))
      where
        ||| The header of a list's `[]`.
        nilHeader : Bits64
        nilHeader = kindId CON

        ||| The cells of a list of `n` characters, one block: `[]` first, then each
        ||| `(::)`, 24 bytes, its tail the next, the last's tail the `[]`. Fills the
        ||| `k`th cell on from byte `i` of the string. Ends: `k` climbs to `n`.
        covering
        unpackFill : Addr STRING -> (i, k, n : Bits64) -> (block : Bits64) -> Op Heap ()
        unpackFill s i k n block =
          if k >= n then pure () else do
            c <- decodeAt s i
            b <- byteAt s i
            let cell = fromWord {k = CON} (block + 8 + 24 * k)
            store64 cell 0 consHeader
            w <- fixnumWord c
            store64 cell 8 w
            tail <- fieldPointer (fromWord {k = CON} (if k + 1 == n then block else block + 8 + 24 * (k + 1)))
            store64 cell 16 tail
            unpackFill s (i + seqLength b) (k + 1) n block
          where
            ||| The header of a list's `(::)`.
            consHeader : Bits64
            consHeader = kindId CON + shiftL 1 (fst (place ConId)) + shiftL 2 (fst (place ConArity))

%cg native flat Runtime.String.Utf8.fastConcat
||| `fastConcat`: a list of strings as one.
export covering
fastConcat : Uniform (List String) -> Uniform String
fastConcat xs = let (MkHeap # r) = concatOp xs MkHeap in r
  where
    ||| A list of strings as one.
    covering
    concatOp : Uniform (List String) -> Op Heap (Uniform String)
    concatOp xs = do
      cell <- conObject xs
      (n, ascii) <- concatMeasure cell 0 True
      r <- newString n
      concatWrite cell r 0
      finish r ascii n
      where
        ||| The bytes of a list of strings, and whether all are ASCII. Ends: the list
        ||| is finite.
        covering
        concatMeasure : Addr CON -> (bytes : Bits64) -> (ascii : Bool) -> Op Heap (Bits64, Bool)
        concatMeasure cell bytes ascii = do
          end <- isNil cell
          if end then pure (bytes, ascii) else do
            w <- load64 cell 8
            t <- load64 cell 16
            s <- fieldObject {k = STRING} w
            h <- headerOf s
            next <- fieldObject {k = CON} t
            concatMeasure next (bytes + bytesOf h) (ascii && asciiOf h)

        ||| The strings of a list copied from `j`. Ends: as `concatMeasure`.
        covering
        concatWrite : Addr CON -> Addr STRING -> (j : Bits64) -> Op Heap ()
        concatWrite cell r j = do
          end <- isNil cell
          if end then pure () else do
            w <- load64 cell 8
            t <- load64 cell 16
            s <- fieldObject {k = STRING} w
            h <- headerOf s
            _ <- copyBytes s 0 r j (bytesOf h) 0
            next <- fieldObject {k = CON} t
            concatWrite next r (j + bytesOf h)
