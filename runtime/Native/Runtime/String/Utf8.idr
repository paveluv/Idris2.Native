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
module Native.Runtime.String.Utf8

import Native.Flat.Uniform as Flat
import Native.Heap
import Native.HeapObj.Header
import Native.HeapObj.Kind as HeapObj
import Native.Port
import Native.Routines
import Native.Runtime.Bits
import Native.Runtime.CodePoint
import Native.Runtime.Memory
import Native.Runtime.Object
import Native.Runtime.OS
import Native.Runtime.Space

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

------------------------------------------------------------------------------
-- The layout

||| The bytes a header counts, and whether it says they are all ASCII.
bytesOf : (header : Bits64) -> Bits64
bytesOf = Object.part HeapObj.Header.StringBytes

asciiOf : (header : Bits64) -> Bool
asciiOf h = Object.part HeapObj.Header.StringAscii h == 1

||| The header of a string of `bytes`.
headerFor : (ascii : Bool) -> (bytes : Bits64) -> Bits64
headerFor ascii bytes =
  HeapObj.Kind.kindId HeapObj.Kind.STRING
    + Bits.shiftL (if ascii then 1 else 0) (fst (HeapObj.Header.place HeapObj.Header.StringAscii))
    + Bits.shiftL bytes (fst (HeapObj.Header.place HeapObj.Header.StringBytes))

||| A string's header.
headerOf : Memory.Addr HeapObj.Kind.STRING -> Heap.Op Heap Bits64
headerOf s = Memory.load64 s 0

||| A new string of `bytes`, its header saying it is ASCII until `finish`
||| sets it, its bytes still to be written, its padding zero.
newString : (bytes : Bits64) -> Heap.Op Heap (Memory.Addr HeapObj.Kind.STRING)
newString bytes = do
  let words = Object.byteWords bytes
  a <- Space.allocate (8 * (1 + words))
  let s = Memory.fromWord {k = HeapObj.Kind.STRING} a
  Memory.store64 s 0 (headerFor True bytes)
  if words == 0 then Heap.pure s else do
    Memory.store64 s (8 * words) 0
    Heap.pure s

||| A new string's header set, and the string as ordinary code holds it.
finish : Memory.Addr HeapObj.Kind.STRING -> (ascii : Bool) -> (bytes : Bits64) -> Heap.Op Heap (Flat.Uniform String)
finish s ascii bytes = do
  Memory.store64 s 0 (headerFor ascii bytes)
  Memory.stringValue s

||| The byte at `i`, and storing one.
byteAt : Memory.Addr HeapObj.Kind.STRING -> (i : Bits64) -> Heap.Op Heap Bits64
byteAt s i = Memory.load8 s (8 + i)

setByte : Memory.Addr HeapObj.Kind.STRING -> (i, b : Bits64) -> Heap.Op Heap ()
setByte s i b = Memory.store8 s (8 + i) b

------------------------------------------------------------------------------
-- UTF-8, at the string's bytes

||| The bytes of the character whose lead byte is `b`.
seqLength : (lead : Bits64) -> Bits64
seqLength = CodePoint.utf8Length

||| The bytes of the character `c`, shortest form.
charBytes : (c : Bits64) -> Bits64
charBytes = CodePoint.utf8Bytes

||| The character whose lead byte is at `i`.
decodeAt : Memory.Addr HeapObj.Kind.STRING -> (i : Bits64) -> Heap.Op Heap Bits64
decodeAt s i = CodePoint.decodeUtf8 s (8 + i)

||| The character `c` written at `j`, its `charBytes c` bytes.
encodeAt : Memory.Addr HeapObj.Kind.STRING -> (j, c : Bits64) -> Heap.Op Heap ()
encodeAt s j c = CodePoint.encodeUtf8 s (8 + j) c

------------------------------------------------------------------------------
-- Loops

||| The characters from byte `i` to `end`: the bytes that are not a
||| continuation byte, `10xxxxxx`. Ends: `i` climbs to `end`.
covering
countChars : Memory.Addr HeapObj.Kind.STRING -> (i, end, count : Bits64) -> Heap.Op Heap Bits64
countChars s i end count =
  if i >= end then Heap.pure count else do
    b <- byteAt s i
    countChars s (i + 1) end (if b .&. 0xC0 == 0x80 then count else count + 1)

||| The byte offset of the `n`th character of a string of the header.
covering
offsetOf : Memory.Addr HeapObj.Kind.STRING -> (header, n : Bits64) -> Heap.Op Heap Bits64
offsetOf s h n =
  if asciiOf h then Heap.pure (if n > bytesOf h then bytesOf h else n)
  else skipChars s 0 (bytesOf h) n
  where
    ||| The byte offset `n` characters after `i`, or `end` if there are fewer.
    ||| Ends: `n` falls to 0, or `i` climbs to `end`.
    covering
    skipChars : Memory.Addr HeapObj.Kind.STRING -> (i, end, n : Bits64) -> Heap.Op Heap Bits64
    skipChars s i end n =
      if n == 0 || i >= end then Heap.pure (if i > end then end else i) else do
        b <- byteAt s i
        skipChars s (i + seqLength b) end (n - 1)

||| Copy `n` bytes from `i` in one string to `j` in another; the OR of the
||| bytes, whose top bit says whether any is not ASCII. Ends: `n` falls to 0.
covering
copyBytes : (from : Memory.Addr HeapObj.Kind.STRING) -> (i : Bits64) -> (to : Memory.Addr HeapObj.Kind.STRING) ->
            (j, n, seen : Bits64) -> Heap.Op Heap Bits64
copyBytes from i to j n seen =
  if n == 0 then Heap.pure seen else do
    b <- byteAt from i
    setByte to j b
    copyBytes from (i + 1) to (j + 1) (n - 1) (seen .|. b)

||| The bytes from `from` to `to` of a string, as a new string: ASCII if the
||| string is, or if the bytes copied are.
covering
slice : Memory.Addr HeapObj.Kind.STRING -> (header, from, to : Bits64) -> Heap.Op Heap (Flat.Uniform String)
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
length : Flat.Uniform String -> Heap.Op Heap Bits64
length str = do
  s <- Memory.stringObject str
  h <- headerOf s
  if asciiOf h then Heap.pure (bytesOf h) else countChars s 0 (bytesOf h) 0

%cg native flat Runtime.String.Utf8.head
||| The first character.
export
head : Flat.Uniform String -> Heap.Op Heap Bits64
head str = do
  s <- Memory.stringObject str
  h <- headerOf s
  if bytesOf h == 0 then Heap.crashOp "idris: the head of an empty string" else decodeAt s 0

%cg native flat Runtime.String.Utf8.tail
||| All but the first character.
export covering
tail : Flat.Uniform String -> Heap.Op Heap (Flat.Uniform String)
tail str = do
  s <- Memory.stringObject str
  h <- headerOf s
  if bytesOf h == 0 then Heap.crashOp "idris: the tail of an empty string" else do
    b <- byteAt s 0
    slice s h (seqLength b) (bytesOf h)

%cg native flat Runtime.String.Utf8.index
||| The character at an index. A negative index comes as a word past every
||| length.
export covering
index : Flat.Uniform String -> (i : Bits64) -> Heap.Op Heap Bits64
index str i = do
  s <- Memory.stringObject str
  h <- headerOf s
  off <- offsetOf s h i
  if off >= bytesOf h then Heap.crashOp "idris: an index outside a string" else decodeAt s off

%cg native flat Runtime.String.Utf8.cons
||| A character, then a string.
export covering
cons : (c : Bits64) -> Flat.Uniform String -> Heap.Op Heap (Flat.Uniform String)
cons c str = do
  s <- Memory.stringObject str
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
append : Flat.Uniform String -> Flat.Uniform String -> Heap.Op Heap (Flat.Uniform String)
append x y = do
  a <- Memory.stringObject x
  b <- Memory.stringObject y
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
reverse : Flat.Uniform String -> Heap.Op Heap (Flat.Uniform String)
reverse str = do
  s <- Memory.stringObject str
  h <- headerOf s
  let n = bytesOf h
  r <- newString n
  reverseFrom s 0 n r
  finish r (asciiOf h) n
  where
    ||| The characters of a string from byte `i` to `n`, each written at the
    ||| mirror of its place in `r`. Ends: `i` climbs to `n`.
    covering
    reverseFrom : Memory.Addr HeapObj.Kind.STRING -> (i, n : Bits64) -> Memory.Addr HeapObj.Kind.STRING ->
                  Heap.Op Heap ()
    reverseFrom s i n r =
      if i >= n then Heap.pure () else do
        b <- byteAt s i
        let k = seqLength b
        _ <- copyBytes s i r (n - i - k) k 0
        reverseFrom s (i + k) n r

%cg native flat Runtime.String.Utf8.substr
||| `len` characters from `start`, both clamped to the string, as Chez's
||| `string-substr` does: a negative one counts as 0, and a start past the
||| end gives the empty string.
export covering
substr : (start, len : Int) -> Flat.Uniform String -> Heap.Op Heap (Flat.Uniform String)
substr start len str = do
  s <- Memory.stringObject str
  h <- headerOf s
  let n = bytesOf h
  count <- if asciiOf h then Heap.pure n else countChars s 0 n 0
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
compare : Flat.Uniform String -> Flat.Uniform String -> Heap.Op Heap Int
compare x y = do
  a <- Memory.stringObject x
  b <- Memory.stringObject y
  ha <- headerOf a
  hb <- headerOf b
  compareFrom a b 0 (bytesOf ha) (bytesOf hb)
  where
    ||| Compare two strings' bytes from `i`: the first difference, else the
    ||| shorter first. Ends: `i` climbs to the shorter's length.
    covering
    compareFrom : Memory.Addr HeapObj.Kind.STRING -> Memory.Addr HeapObj.Kind.STRING -> (i, na, nb : Bits64) ->
                  Heap.Op Heap Int
    compareFrom a b i na nb =
      if i >= na || i >= nb then Heap.pure (if na < nb then -1 else if na > nb then 1 else 0) else do
        p <- byteAt a i
        q <- byteAt b i
        if p < q then Heap.pure (-1) else if p > q then Heap.pure 1 else compareFrom a b (i + 1) na nb

------------------------------------------------------------------------------
-- Lists of characters and of strings: `prelude`'s `fastPack`, `fastUnpack`
-- and `fastConcat`. A list is a `CON` object: `[]` of constructor id 0 and
-- no fields, often the static one; `(::)` of id 1, its head then its tail.
-- A character in a field is its fixnum, a string or a list a pointer.

||| Whether a list's cell is `[]`.
isNil : Memory.Addr HeapObj.Kind.CON -> Heap.Op Heap Bool
isNil cell = do
  h <- Memory.load64 cell 0
  Heap.pure (Object.part HeapObj.Header.ConId h == 0)

%cg native flat Runtime.String.Utf8.fastPack
||| `fastPack`: a list of characters as a string.
export covering
fastPack : Flat.Uniform (List Char) -> Flat.Uniform String
fastPack xs = let (Heap.MkHeap # r) = packOp xs Heap.MkHeap in r
  where
    ||| A list of characters as a string.
    covering
    packOp : Flat.Uniform (List Char) -> Heap.Op Heap (Flat.Uniform String)
    packOp xs = do
      cell <- Memory.conObject xs
      (n, seen) <- packMeasure cell 0 0
      s <- newString n
      packWrite cell s 0
      finish s (seen < 0x80) n
      where
        ||| The bytes the characters of a list take, and the OR of their code
        ||| points. Ends: the list is finite, each step one cell on.
        covering
        packMeasure : Memory.Addr HeapObj.Kind.CON -> (bytes, seen : Bits64) -> Heap.Op Heap (Bits64, Bits64)
        packMeasure cell bytes seen = do
          end <- isNil cell
          if end then Heap.pure (bytes, seen) else do
            c <- Memory.load64 cell 8
            t <- Memory.load64 cell 16
            next <- Memory.fieldObject {k = HeapObj.Kind.CON} t
            let ch = Memory.fixnumOf c
            packMeasure next (bytes + charBytes ch) (seen .|. ch)

        ||| The characters of a list written from `j`. Ends: as `packMeasure`.
        covering
        packWrite : Memory.Addr HeapObj.Kind.CON -> Memory.Addr HeapObj.Kind.STRING -> (j : Bits64) -> Heap.Op Heap ()
        packWrite cell s j = do
          end <- isNil cell
          if end then Heap.pure () else do
            c <- Memory.load64 cell 8
            t <- Memory.load64 cell 16
            next <- Memory.fieldObject {k = HeapObj.Kind.CON} t
            let ch = Memory.fixnumOf c
            encodeAt s j ch
            packWrite next s (j + charBytes ch)

%cg native flat Runtime.String.Utf8.fastUnpack
||| `fastUnpack`: a string as a list of characters.
export covering
fastUnpack : Flat.Uniform String -> Flat.Uniform (List Char)
fastUnpack str = let (Heap.MkHeap # r) = unpackOp str Heap.MkHeap in r
  where
    ||| A string as a list of characters.
    covering
    unpackOp : Flat.Uniform String -> Heap.Op Heap (Flat.Uniform (List Char))
    unpackOp str = do
      s <- Memory.stringObject str
      h <- headerOf s
      n <- if asciiOf h then Heap.pure (bytesOf h) else countChars s 0 (bytesOf h) 0
      block <- Space.allocate (8 + 24 * n)
      Memory.store64 (Memory.fromWord {k = HeapObj.Kind.CON} block) 0 nilHeader
      unpackFill s 0 0 n block
      Memory.conValue (Memory.fromWord (if n == 0 then block else block + 8))
      where
        ||| The header of a list's `[]`.
        nilHeader : Bits64
        nilHeader = HeapObj.Kind.kindId HeapObj.Kind.CON

        ||| The cells of a list of `n` characters, one block: `[]` first, then each
        ||| `(::)`, 24 bytes, its tail the next, the last's tail the `[]`. Fills the
        ||| `k`th cell on from byte `i` of the string. Ends: `k` climbs to `n`.
        covering
        unpackFill : Memory.Addr HeapObj.Kind.STRING -> (i, k, n : Bits64) -> (block : Bits64) -> Heap.Op Heap ()
        unpackFill s i k n block =
          if k >= n then Heap.pure () else do
            c <- decodeAt s i
            b <- byteAt s i
            let cell = Memory.fromWord {k = HeapObj.Kind.CON} (block + 8 + 24 * k)
            Memory.store64 cell 0 consHeader
            w <- Memory.fixnumWord c
            Memory.store64 cell 8 w
            tail <- Memory.fieldPointer
              (Memory.fromWord {k = HeapObj.Kind.CON} (if k + 1 == n then block else block + 8 + 24 * (k + 1)))
            Memory.store64 cell 16 tail
            unpackFill s (i + seqLength b) (k + 1) n block
          where
            ||| The header of a list's `(::)`.
            consHeader : Bits64
            consHeader = HeapObj.Kind.kindId HeapObj.Kind.CON
              + Bits.shiftL 1 (fst (HeapObj.Header.place HeapObj.Header.ConId))
              + Bits.shiftL 2 (fst (HeapObj.Header.place HeapObj.Header.ConArity))

%cg native flat Runtime.String.Utf8.fastConcat
||| `fastConcat`: a list of strings as one.
export covering
fastConcat : Flat.Uniform (List String) -> Flat.Uniform String
fastConcat xs = let (Heap.MkHeap # r) = concatOp xs Heap.MkHeap in r
  where
    ||| A list of strings as one.
    covering
    concatOp : Flat.Uniform (List String) -> Heap.Op Heap (Flat.Uniform String)
    concatOp xs = do
      cell <- Memory.conObject xs
      (n, ascii) <- concatMeasure cell 0 True
      r <- newString n
      concatWrite cell r 0
      finish r ascii n
      where
        ||| The bytes of a list of strings, and whether all are ASCII. Ends: the list
        ||| is finite.
        covering
        concatMeasure : Memory.Addr HeapObj.Kind.CON -> (bytes : Bits64) -> (ascii : Bool) ->
                        Heap.Op Heap (Bits64, Bool)
        concatMeasure cell bytes ascii = do
          end <- isNil cell
          if end then Heap.pure (bytes, ascii) else do
            w <- Memory.load64 cell 8
            t <- Memory.load64 cell 16
            s <- Memory.fieldObject {k = HeapObj.Kind.STRING} w
            h <- headerOf s
            next <- Memory.fieldObject {k = HeapObj.Kind.CON} t
            concatMeasure next (bytes + bytesOf h) (ascii && asciiOf h)

        ||| The strings of a list copied from `j`. Ends: as `concatMeasure`.
        covering
        concatWrite : Memory.Addr HeapObj.Kind.CON -> Memory.Addr HeapObj.Kind.STRING -> (j : Bits64) -> Heap.Op Heap ()
        concatWrite cell r j = do
          end <- isNil cell
          if end then Heap.pure () else do
            w <- Memory.load64 cell 8
            t <- Memory.load64 cell 16
            s <- Memory.fieldObject {k = HeapObj.Kind.STRING} w
            h <- headerOf s
            _ <- copyBytes s 0 r j (bytesOf h) 0
            next <- Memory.fieldObject {k = HeapObj.Kind.CON} t
            concatWrite next r (j + bytesOf h)

------------------------------------------------------------------------------
-- Numbers as text

||| A magnitude in decimal, after a `-` if it is negative: an ASCII string.
covering
decimal : (negative : Bool) -> (magnitude : Bits64) -> Heap.Op Heap (Flat.Uniform String)
decimal negative m = do
  let sign = if negative then 1 else 0
      bytes = sign + decimalDigits m
  s <- newString bytes
  if negative then setByte s 0 45 else Heap.pure ()
  writeDigits s bytes m
  finish s True bytes
  where
    ||| How many decimal digits a word has.
    covering
    decimalDigits : Bits64 -> Bits64
    decimalDigits n = if n < 10 then 1 else 1 + decimalDigits (n `div` 10)

    ||| A word's decimal digits written to end at byte `end`, the last digit
    ||| before it.
    covering
    writeDigits : Memory.Addr HeapObj.Kind.STRING -> (end, n : Bits64) -> Heap.Op Heap ()
    writeDigits s end n = do
      setByte s (end - 1) (48 + n `mod` 10)
      if n < 10 then Heap.pure () else writeDigits s (end - 1) (n `div` 10)

%cg native flat Runtime.String.Utf8.showSigned
||| A signed word in decimal, as Chez writes it. The most negative word's
||| magnitude is its own pattern, unsigned.
export covering
showSigned : (n : Int) -> Heap.Op Heap (Flat.Uniform String)
showSigned n = if n < 0 then decimal True (cast {to = Bits64} (0 - n)) else decimal False (cast n)

%cg native flat Runtime.String.Utf8.showUnsigned
||| A word, unsigned, in decimal.
export covering
showUnsigned : (n : Bits64) -> Heap.Op Heap (Flat.Uniform String)
showUnsigned = decimal False

||| The string routines under UTF-8, each checked against its port: the
||| record the code generator reads for the functions generated code calls.
export covering
strings : Routines.StringRoutines (Port.PortTy (\k => Memory.Addr k))
strings =
  Routines.MkStringRoutines
    { length = Utf8.length, head = Utf8.head, tail = Utf8.tail, index = Utf8.index, cons = Utf8.cons
    , append = Utf8.append, reverse = Utf8.reverse, substr = Utf8.substr, compare = Utf8.compare
    , showSigned = Utf8.showSigned, showUnsigned = Utf8.showUnsigned }

%cg native flat Runtime.String.Utf8.prim__putStr
||| `putStr`: the string's bytes written to the standard output, all of
||| them. Nothing is buffered, so nothing waits to be flushed.
export covering
prim__putStr : Flat.Uniform String -> PrimIO ()
prim__putStr str w = let (Heap.MkHeap # ()) = putOp str Heap.MkHeap in MkIORes () w
  where
    covering
    putOp : Flat.Uniform String -> Heap.Op Heap ()
    putOp str = do
      s <- Memory.stringObject str
      h <- headerOf s
      OS.osWriteAll OS.stdout (Memory.toWord s + 8) (bytesOf h)
