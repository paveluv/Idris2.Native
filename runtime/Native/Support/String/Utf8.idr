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
module Native.Support.String.Utf8

import Native.Flat.Uniform as Flat
import Native.HeapObj.Shape as HeapObj
import Native.Port
import Native.Primitive.DoubleBits
import Native.Runtime.Bits
import Native.Runtime.Heap as Runtime
import Native.Runtime.Memory
import Native.Runtime.OS
import Native.Runtime.PortTy as Runtime
import Native.Runtime.Raw as Runtime
import Native.Runtime.Space
import Native.Support.CodePoint
import Native.Support.Double.Between
import Native.Support.Double.Limbs
import Native.Support.Double.Nearest
import Native.Support.Double.Shortest
import Native.Support.Obj
import Native.Types.Header
import Native.Types.Kind
import Native.Types.StringRoutine

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

------------------------------------------------------------------------------
-- The layout

||| The bytes a header counts, and whether it says they are all ASCII.
bytesOf : (header : Bits64) -> Bits64
bytesOf = Types.Header.readPart Types.Header.StringBytes

asciiOf : (header : Bits64) -> Bool
asciiOf h = Types.Header.readPart Types.Header.StringAscii h == 1

||| The header of a string of `bytes`.
headerFor : (ascii : Bool) -> (bytes : Bits64) -> Bits64
headerFor ascii bytes =
  Types.Header.fixedWord Types.Kind.STRING
    + Types.Header.partBits Types.Header.StringAscii (if ascii then 1 else 0)
    + Types.Header.partBits Types.Header.StringBytes bytes

||| The object a string is: a string is always an object.
export
stringObject : Flat.Uniform String -> Runtime.Heap.Op Runtime.Heap (Obj Types.Kind.STRING)
stringObject s = Obj.valueObject s

||| A string's header.
headerOf : Obj Types.Kind.STRING -> Runtime.Heap.Op Runtime.Heap Bits64
headerOf s = Obj.load64 s 0

||| A new string of `bytes`, its header saying it is ASCII until `finish`
||| sets it, its bytes still to be written, its padding zero.
newString : (bytes : Bits64) -> Runtime.Heap.Op Runtime.Heap (Obj Types.Kind.STRING)
newString bytes = do
  let header = headerFor True bytes
      words = HeapObj.Shape.objectWordsOf header
  a <- Runtime.Space.allocate (8 * words)
  let s = Obj.objectAt {k = Types.Kind.STRING} a
  Obj.store64 s 0 header
  if words == 1 then Runtime.Heap.pure s else do
    Obj.store64 s (8 * (words - 1)) 0
    Runtime.Heap.pure s

||| A new string's header set, and the string as ordinary code holds it.
finish : Obj Types.Kind.STRING -> (ascii : Bool) -> (bytes : Bits64) -> Runtime.Heap.Op Runtime.Heap (Flat.Uniform String)
finish s ascii bytes = do
  Obj.store64 s 0 (headerFor ascii bytes)
  Obj.objectValue s

||| The byte at `i`, and storing one.
byteAt : Obj Types.Kind.STRING -> (i : Bits64) -> Runtime.Heap.Op Runtime.Heap Bits64
byteAt s i = Obj.load8 s (8 + i)

setByte : Obj Types.Kind.STRING -> (i, b : Bits64) -> Runtime.Heap.Op Runtime.Heap ()
setByte s i b = Obj.store8 s (8 + i) b

------------------------------------------------------------------------------
-- UTF-8, at the string's bytes

||| The bytes of the character whose lead byte is `b`.
seqLength : (lead : Bits64) -> Bits64
seqLength = CodePoint.utf8Length

||| The bytes of the character `c`, shortest form.
charBytes : (c : Bits64) -> Bits64
charBytes = CodePoint.utf8Bytes

||| The character whose lead byte is at `i`.
decodeAt : Obj Types.Kind.STRING -> (i : Bits64) -> Runtime.Heap.Op Runtime.Heap Bits64
decodeAt s i = CodePoint.decodeUtf8 s (8 + i)

||| The character `c` written at `j`, its `charBytes c` bytes.
encodeAt : Obj Types.Kind.STRING -> (j, c : Bits64) -> Runtime.Heap.Op Runtime.Heap ()
encodeAt s j c = CodePoint.encodeUtf8 s (8 + j) c

------------------------------------------------------------------------------
-- Loops

||| The characters from byte `i` to `end`: the bytes that are not a
||| continuation byte, `10xxxxxx`. Ends: `i` climbs to `end`.
covering
countChars : Obj Types.Kind.STRING -> (i, end, count : Bits64) -> Runtime.Heap.Op Runtime.Heap Bits64
countChars s i end count =
  if i >= end then Runtime.Heap.pure count else do
    b <- byteAt s i
    countChars s (i + 1) end (if b .&. 0xC0 == 0x80 then count else count + 1)

||| The byte offset of the `n`th character of a string of the header.
covering
offsetOf : Obj Types.Kind.STRING -> (header, n : Bits64) -> Runtime.Heap.Op Runtime.Heap Bits64
offsetOf s h n =
  if asciiOf h then Runtime.Heap.pure (if n > bytesOf h then bytesOf h else n)
  else skipChars s 0 (bytesOf h) n
  where
    ||| The byte offset `n` characters after `i`, or `end` if there are fewer.
    ||| Ends: `n` falls to 0, or `i` climbs to `end`.
    covering
    skipChars : Obj Types.Kind.STRING -> (i, end, n : Bits64) -> Runtime.Heap.Op Runtime.Heap Bits64
    skipChars s i end n =
      if n == 0 || i >= end then Runtime.Heap.pure (if i > end then end else i) else do
        b <- byteAt s i
        skipChars s (i + seqLength b) end (n - 1)

||| Copy `n` bytes from `i` in one string to `j` in another; the OR of the
||| bytes, whose top bit says whether any is not ASCII. Ends: `n` falls to 0.
covering
copyBytes : (from : Obj Types.Kind.STRING) -> (i : Bits64) -> (to : Obj Types.Kind.STRING) ->
            (j, n, seen : Bits64) -> Runtime.Heap.Op Runtime.Heap Bits64
copyBytes from i to j n seen =
  if n == 0 then Runtime.Heap.pure seen else do
    b <- byteAt from i
    setByte to j b
    copyBytes from (i + 1) to (j + 1) (n - 1) (seen .|. b)

||| The bytes from `from` to `to` of a string, as a new string: ASCII if the
||| string is, or if the bytes copied are.
covering
slice : Obj Types.Kind.STRING -> (header, from, to : Bits64) -> Runtime.Heap.Op Runtime.Heap (Flat.Uniform String)
slice s h from to = do
  let n = to - from
  r <- newString n
  seen <- copyBytes s from r 0 n 0
  finish r (asciiOf h || seen < 0x80) n

------------------------------------------------------------------------------
-- The primitives

%cg native flat Support.String.Utf8.length
||| The characters of a string.
export covering
length : Runtime.PortTy Runtime.Memory.Addr (Types.StringRoutine.port Types.StringRoutine.Length)
length str = do
  s <- stringObject str
  h <- headerOf s
  if asciiOf h then Runtime.Heap.pure (bytesOf h) else countChars s 0 (bytesOf h) 0

%cg native flat Support.String.Utf8.head
||| The first character.
export
head : Runtime.PortTy Runtime.Memory.Addr (Types.StringRoutine.port Types.StringRoutine.Head)
head str = do
  s <- stringObject str
  h <- headerOf s
  if bytesOf h == 0 then Runtime.Heap.crashOp "idris: the head of an empty string" else decodeAt s 0

%cg native flat Support.String.Utf8.tail
||| All but the first character.
export covering
tail : Runtime.PortTy Runtime.Memory.Addr (Types.StringRoutine.port Types.StringRoutine.Tail)
tail str = do
  s <- stringObject str
  h <- headerOf s
  if bytesOf h == 0 then Runtime.Heap.crashOp "idris: the tail of an empty string" else do
    b <- byteAt s 0
    slice s h (seqLength b) (bytesOf h)

%cg native flat Support.String.Utf8.index
||| The character at an index. A negative index comes as a word past every
||| length.
export covering
index : Runtime.PortTy Runtime.Memory.Addr (Types.StringRoutine.port Types.StringRoutine.Index)
index str i = do
  s <- stringObject str
  h <- headerOf s
  off <- offsetOf s h i
  if off >= bytesOf h then Runtime.Heap.crashOp "idris: an index outside a string" else decodeAt s off

%cg native flat Support.String.Utf8.cons
||| A character, then a string.
export covering
cons : Runtime.PortTy Runtime.Memory.Addr (Types.StringRoutine.port Types.StringRoutine.Cons)
cons c str = do
  s <- stringObject str
  h <- headerOf s
  let k = charBytes c
  let n = bytesOf h
  r <- newString (k + n)
  encodeAt r 0 c
  _ <- copyBytes s 0 r k n 0
  finish r (c < 0x80 && asciiOf h) (k + n)

%cg native flat Support.String.Utf8.append
||| One string, then another.
export covering
append : Runtime.PortTy Runtime.Memory.Addr (Types.StringRoutine.port Types.StringRoutine.Append)
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

%cg native flat Support.String.Utf8.reverse
||| The characters in the other order.
export covering
reverse : Runtime.PortTy Runtime.Memory.Addr (Types.StringRoutine.port Types.StringRoutine.Reverse)
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
    reverseFrom : Obj Types.Kind.STRING -> (i, n : Bits64) -> Obj Types.Kind.STRING ->
                  Runtime.Heap.Op Runtime.Heap ()
    reverseFrom s i n r =
      if i >= n then Runtime.Heap.pure () else do
        b <- byteAt s i
        let k = seqLength b
        _ <- copyBytes s i r (n - i - k) k 0
        reverseFrom s (i + k) n r

%cg native flat Support.String.Utf8.substr
||| `len` characters from `start`, both clamped to the string, as Chez's
||| `string-substr` does: a negative one counts as 0, and a start past the
||| end gives the empty string.
export covering
substr : Runtime.PortTy Runtime.Memory.Addr (Types.StringRoutine.port Types.StringRoutine.Substr)
substr start len str = do
  s <- stringObject str
  h <- headerOf s
  let n = bytesOf h
  count <- if asciiOf h then Runtime.Heap.pure n else countChars s 0 n 0
  let b = if start < 0 then 0 else cast {to = Bits64} start
  let x = if len < 0 then 0 else cast {to = Bits64} len
  let e = if x > count - b then count else b + x
  if b > count then slice s h 0 0 else do
    from <- offsetOf s h b
    to <- offsetOf s h e
    slice s h from to

%cg native flat Support.String.Utf8.compare
||| The order of two strings, -1, 0 or 1: by code point, which is the order
||| of their UTF-8 bytes.
export covering
compare : Runtime.PortTy Runtime.Memory.Addr (Types.StringRoutine.port Types.StringRoutine.Compare)
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
    compareFrom : Obj Types.Kind.STRING -> Obj Types.Kind.STRING -> (i, na, nb : Bits64) ->
                  Runtime.Heap.Op Runtime.Heap Int
    compareFrom a b i na nb =
      if i >= na || i >= nb then Runtime.Heap.pure (if na < nb then -1 else if na > nb then 1 else 0) else do
        p <- byteAt a i
        q <- byteAt b i
        if p < q then Runtime.Heap.pure (-1) else if p > q then Runtime.Heap.pure 1 else compareFrom a b (i + 1) na nb

------------------------------------------------------------------------------
-- Lists of characters and of strings: `prelude`'s `fastPack`, `fastUnpack`
-- and `fastConcat`. A list is a `CON` object: `[]` of constructor id 0 and
-- no fields, often the static one; `(::)` of id 1, its head then its tail.
-- A character in a field is its fixnum, a string or a list a pointer.

||| Whether a list's cell is `[]`.
isNil : Obj Types.Kind.CON -> Runtime.Heap.Op Runtime.Heap Bool
isNil cell = do
  h <- Obj.load64 cell 0
  Runtime.Heap.pure (Types.Header.readPart Types.Header.ConId h == 0)

%cg native flat Support.String.Utf8.fastPack
||| `fastPack`: a list of characters as a string.
export covering
fastPack : Flat.Uniform (List Char) -> Flat.Uniform String
fastPack xs = let (Runtime.MkHeap # r) = packOp xs Runtime.MkHeap in r
  where
    ||| A list of characters as a string.
    covering
    packOp : Flat.Uniform (List Char) -> Runtime.Heap.Op Runtime.Heap (Flat.Uniform String)
    packOp xs = do
      cell <- Obj.valueObject {k = Types.Kind.CON} xs
      (n, seen) <- packMeasure cell 0 0
      s <- newString n
      packWrite cell s 0
      finish s (seen < 0x80) n
      where
        ||| The bytes the characters of a list take, and the OR of their code
        ||| points. Ends: the list is finite, each step one cell on.
        covering
        packMeasure : Obj Types.Kind.CON -> (bytes, seen : Bits64) -> Runtime.Heap.Op Runtime.Heap (Bits64, Bits64)
        packMeasure cell bytes seen = do
          end <- isNil cell
          if end then Runtime.Heap.pure (bytes, seen) else do
            c <- Obj.load64 cell 8
            t <- Obj.load64 cell 16
            next <- Obj.fieldObject {k = Types.Kind.CON} t
            let ch = Runtime.Memory.fixnumOf c
            packMeasure next (bytes + charBytes ch) (seen .|. ch)

        ||| The characters of a list written from `j`. Ends: as `packMeasure`.
        covering
        packWrite : Obj Types.Kind.CON -> Obj Types.Kind.STRING -> (j : Bits64) -> Runtime.Heap.Op Runtime.Heap ()
        packWrite cell s j = do
          end <- isNil cell
          if end then Runtime.Heap.pure () else do
            c <- Obj.load64 cell 8
            t <- Obj.load64 cell 16
            next <- Obj.fieldObject {k = Types.Kind.CON} t
            let ch = Runtime.Memory.fixnumOf c
            encodeAt s j ch
            packWrite next s (j + charBytes ch)

%cg native flat Support.String.Utf8.fastUnpack
||| `fastUnpack`: a string as a list of characters.
export covering
fastUnpack : Flat.Uniform String -> Flat.Uniform (List Char)
fastUnpack str = let (Runtime.MkHeap # r) = unpackOp str Runtime.MkHeap in r
  where
    ||| A string as a list of characters.
    covering
    unpackOp : Flat.Uniform String -> Runtime.Heap.Op Runtime.Heap (Flat.Uniform (List Char))
    unpackOp str = do
      s <- stringObject str
      h <- headerOf s
      n <- if asciiOf h then Runtime.Heap.pure (bytesOf h) else countChars s 0 (bytesOf h) 0
      block <- Runtime.Space.allocate (8 + 24 * n)
      Obj.store64 (Obj.objectAt {k = Types.Kind.CON} block) 0 nilHeader
      unpackFill s 0 0 n block
      Obj.objectValue (Obj.objectAt {k = Types.Kind.CON} (if n == 0 then block else Runtime.Raw.offset block 8))
      where
        ||| The header of a list's `[]`.
        nilHeader : Bits64
        nilHeader = Types.Header.fixedWord Types.Kind.CON

        ||| The cells of a list of `n` characters, one block: `[]` first, then each
        ||| `(::)`, 24 bytes, its tail the next, the last's tail the `[]`. Fills the
        ||| `k`th cell on from byte `i` of the string. Ends: `k` climbs to `n`.
        covering
        unpackFill : Obj Types.Kind.STRING -> (i, k, n : Bits64) -> (block : Raw) -> Runtime.Heap.Op Runtime.Heap ()
        unpackFill s i k n block =
          if k >= n then Runtime.Heap.pure () else do
            c <- decodeAt s i
            b <- byteAt s i
            let cell = Obj.objectAt {k = Types.Kind.CON} (Runtime.Raw.offset block (8 + 24 * k))
            Obj.store64 cell 0 consHeader
            w <- Runtime.Memory.fixnumWord c
            Obj.store64 cell 8 w
            tail <- Obj.fieldPointer
              (Obj.objectAt {k = Types.Kind.CON} (if k + 1 == n then block else Runtime.Raw.offset block (8 + 24 * (k + 1))))
            Obj.store64 cell 16 tail
            unpackFill s (i + seqLength b) (k + 1) n block
          where
            ||| The header of a list's `(::)`.
            consHeader : Bits64
            consHeader = Types.Header.fixedWord Types.Kind.CON
              + Types.Header.partBits Types.Header.ConId 1
              + Types.Header.partBits Types.Header.ConArity 2

%cg native flat Support.String.Utf8.fastConcat
||| `fastConcat`: a list of strings as one.
export covering
fastConcat : Flat.Uniform (List String) -> Flat.Uniform String
fastConcat xs = let (Runtime.MkHeap # r) = concatOp xs Runtime.MkHeap in r
  where
    ||| A list of strings as one.
    covering
    concatOp : Flat.Uniform (List String) -> Runtime.Heap.Op Runtime.Heap (Flat.Uniform String)
    concatOp xs = do
      cell <- Obj.valueObject {k = Types.Kind.CON} xs
      (n, ascii) <- concatMeasure cell 0 True
      r <- newString n
      concatWrite cell r 0
      finish r ascii n
      where
        ||| The bytes of a list of strings, and whether all are ASCII. Ends: the list
        ||| is finite.
        covering
        concatMeasure : Obj Types.Kind.CON -> (bytes : Bits64) -> (ascii : Bool) ->
                        Runtime.Heap.Op Runtime.Heap (Bits64, Bool)
        concatMeasure cell bytes ascii = do
          end <- isNil cell
          if end then Runtime.Heap.pure (bytes, ascii) else do
            w <- Obj.load64 cell 8
            t <- Obj.load64 cell 16
            s <- Obj.fieldObject {k = Types.Kind.STRING} w
            h <- headerOf s
            next <- Obj.fieldObject {k = Types.Kind.CON} t
            concatMeasure next (bytes + bytesOf h) (ascii && asciiOf h)

        ||| The strings of a list copied from `j`. Ends: as `concatMeasure`.
        covering
        concatWrite : Obj Types.Kind.CON -> Obj Types.Kind.STRING -> (j : Bits64) -> Runtime.Heap.Op Runtime.Heap ()
        concatWrite cell r j = do
          end <- isNil cell
          if end then Runtime.Heap.pure () else do
            w <- Obj.load64 cell 8
            t <- Obj.load64 cell 16
            s <- Obj.fieldObject {k = Types.Kind.STRING} w
            h <- headerOf s
            _ <- copyBytes s 0 r j (bytesOf h) 0
            next <- Obj.fieldObject {k = Types.Kind.CON} t
            concatWrite next r (j + bytesOf h)

------------------------------------------------------------------------------
-- Numbers as text

||| How many decimal digits a word has.
covering
decimalDigits : Bits64 -> Bits64
decimalDigits n = if n < 10 then 1 else 1 + decimalDigits (n `div` 10)

||| A word's decimal digits written to end at byte `end`, the last digit
||| before it.
covering
writeDigits : Obj Types.Kind.STRING -> (end, n : Bits64) -> Runtime.Heap.Op Runtime.Heap ()
writeDigits s end n = do
  setByte s (end - 1) (48 + n `mod` 10)
  if n < 10 then Runtime.Heap.pure () else writeDigits s (end - 1) (n `div` 10)

||| A magnitude in decimal, after a `-` if it is negative: an ASCII string.
covering
decimal : (negative : Bool) -> (magnitude : Bits64) -> Runtime.Heap.Op Runtime.Heap (Flat.Uniform String)
decimal negative m = do
  let sign = if negative then 1 else 0
      bytes = sign + decimalDigits m
  s <- newString bytes
  if negative then setByte s 0 45 else Runtime.Heap.pure ()
  writeDigits s bytes m
  finish s True bytes

%cg native flat Support.String.Utf8.showSigned
||| A signed word in decimal, as Chez writes it. The most negative word's
||| magnitude is its own pattern, unsigned.
export covering
showSigned : Runtime.PortTy Runtime.Memory.Addr (Types.StringRoutine.port Types.StringRoutine.ShowSigned)
showSigned n = if n < 0 then decimal True (cast {to = Bits64} (0 - n)) else decimal False (cast n)

%cg native flat Support.String.Utf8.showUnsigned
||| A word, unsigned, in decimal.
export covering
showUnsigned : Runtime.PortTy Runtime.Memory.Addr (Types.StringRoutine.port Types.StringRoutine.ShowUnsigned)
showUnsigned = decimal False

%cg native flat Support.String.Utf8.showDouble
||| A double in decimal: the shortest digits that read back to it (Dragonbox,
||| `Native.Support.Double.Shortest`), as Chez lays them out (`decimalText`),
||| and `+nan.0`, `+inf.0`, `-inf.0`, `0.0` and `-0.0` as Chez writes them.
||| Where two digits of the last place are as close to the double, the even
||| one, where Chez takes the upper; and a subnormal double without the
||| `|n` that Chez writes after it, the bits of its significand.
export covering
showDouble : Runtime.PortTy Runtime.Memory.Addr (Types.StringRoutine.port Types.StringRoutine.ShowDouble)
showDouble x =
  let w = doubleBits x
      negative = w `shiftR` 63 == 1
      be = (w `shiftR` 52) .&. 0x7FF
      f = w .&. 0xFFFFFFFFFFFFF
  in if be == 0x7FF
        -- +nan.0, -inf.0, +inf.0
        then (if f /= 0 then packed 6 0x302E6E616E2B else if negative then packed 6 0x302E666E692D else packed 6 0x302E666E692B)
     else if be == 0 && f == 0
        -- -0.0, 0.0
        then (if negative then packed 4 0x302E302D else packed 3 0x302E30)
     else case shortest f be of
       (sig, e10) => decimalText negative sig e10
  where
    ||| A short ASCII text, its bytes in a word, the first lowest: a new string
    ||| of its `n` bytes.
    covering
    packed : (n, bytes : Bits64) -> Runtime.Heap.Op Runtime.Heap (Flat.Uniform String)
    packed n w = do
      s <- newString n
      write s 0 w
      finish s True n
      where
        covering
        write : Obj Types.Kind.STRING -> (i, rest : Bits64) -> Runtime.Heap.Op Runtime.Heap ()
        write s i rest = if i >= n then Runtime.Heap.pure () else do
          setByte s i (rest .&. 0xFF)
          write s (i + 1) (rest `shiftR` 8)

    ||| A double's shortest digits, `significand` scaled by `10^exponent`, as
    ||| Chez lays them out: positional where the first digit's power of ten,
    ||| `e`, is from -3 to 9 (`0.001`, `1500.0`, `1.25`, with a digit after the
    ||| point always), else as a digit, the others after a point, and `e`
    ||| (`1e21`, `1.5e-7`); after a `-` if the double is negative.
    covering
    decimalText : (negative : Bool) -> (significand : Bits64) -> (exponent : Int) ->
                  Runtime.Heap.Op Runtime.Heap (Flat.Uniform String)
    decimalText negative sig e10 =
      let n = decimalDigits sig
          e = e10 + cast n - 1
          sign : Bits64 = if negative then 1 else 0
      in if e > -4 && e < 10 then positional n e sign else exponential n e sign
      where
        ||| 10 to the power.
        covering
        power : Bits64 -> Bits64
        power 0 = 1
        power k = 10 * power (k - 1)

        ||| `count` digits of a word, leading zeros included, ending at byte
        ||| `end`.
        covering
        writeFixed : Obj Types.Kind.STRING -> (end, count, v : Bits64) -> Runtime.Heap.Op Runtime.Heap ()
        writeFixed s end 0 v = Runtime.Heap.pure ()
        writeFixed s end count v = do
          setByte s (end - 1) (48 + v `mod` 10)
          writeFixed s (end - 1) (count - 1) (v `div` 10)

        ||| `count` zeros from byte `i`.
        covering
        writeZeros : Obj Types.Kind.STRING -> (i, count : Bits64) -> Runtime.Heap.Op Runtime.Heap ()
        writeZeros s i 0 = Runtime.Heap.pure ()
        writeZeros s i count = do
          setByte s i 48
          writeZeros s (i + 1) (count - 1)

        ||| A new string of the bytes, its `-` written if the double is negative.
        covering
        start : (sign, bytes : Bits64) -> Runtime.Heap.Op Runtime.Heap (Obj Types.Kind.STRING)
        start sign bytes = do
          s <- newString bytes
          if sign == 1 then setByte s 0 45 else Runtime.Heap.pure ()
          Runtime.Heap.pure s

        covering
        positional : (n : Bits64) -> (e : Int) -> (sign : Bits64) -> Runtime.Heap.Op Runtime.Heap (Flat.Uniform String)
        positional n e sign =
          if e < 0 then do
            -- 0.001: the point, -e - 1 zeros, the digits
            let zeros = cast {to = Bits64} (negate e - 1)
                bytes = sign + 2 + zeros + n
            s <- start sign bytes
            setByte s sign 48
            setByte s (sign + 1) 46
            writeZeros s (sign + 2) zeros
            writeFixed s bytes n sig
            finish s True bytes
          else let whole = cast {to = Bits64} e + 1 in
            if whole >= n then do
              -- 1500.0: the digits, zeros to the point, a zero after it
              let bytes = sign + whole + 2
              s <- start sign bytes
              writeDigits s (sign + n) sig
              writeZeros s (sign + n) (whole - n)
              setByte s (sign + whole) 46
              setByte s (sign + whole + 1) 48
              finish s True bytes
            else do
              -- 1.25: the digits with the point among them
              let fraction = n - whole
                  d = power fraction
                  bytes = sign + n + 1
              s <- start sign bytes
              writeFixed s (sign + whole) whole (sig `div` d)
              setByte s (sign + whole) 46
              writeFixed s bytes fraction (sig `mod` d)
              finish s True bytes

        covering
        exponential : (n : Bits64) -> (e : Int) -> (sign : Bits64) -> Runtime.Heap.Op Runtime.Heap (Flat.Uniform String)
        exponential n e sign = do
          let rest = n - 1
              d = power rest
              mantissa = if rest == 0 then 1 else 2 + rest
              magnitude = cast {to = Bits64} (if e < 0 then negate e else e)
              minus : Bits64 = if e < 0 then 1 else 0
              bytes = sign + mantissa + 1 + minus + decimalDigits magnitude
          s <- start sign bytes
          setByte s sign (48 + sig `div` d)
          if rest == 0 then Runtime.Heap.pure () else do
            setByte s (sign + 1) 46
            writeFixed s (sign + mantissa) rest (sig `mod` d)
          setByte s (sign + mantissa) 101
          if minus == 1 then setByte s (sign + mantissa + 1) 45 else Runtime.Heap.pure ()
          writeDigits s bytes magnitude
          finish s True bytes

%cg native flat Support.String.Utf8.prim__putStr
||| `putStr`: the string's bytes written to the standard output, all of
||| them. Nothing is buffered, so nothing waits to be flushed.
export covering
prim__putStr : Flat.Uniform String -> PrimIO ()
prim__putStr str w = let (Runtime.MkHeap # ()) = putOp str Runtime.MkHeap in MkIORes () w
  where
    covering
    putOp : Flat.Uniform String -> Runtime.Heap.Op Runtime.Heap ()
    putOp str = do
      s <- stringObject str
      h <- headerOf s
      Runtime.OS.osWriteAll Runtime.OS.stdout (Obj.objectBytes s 8) (bytesOf h)

%cg native flat Support.String.Utf8.prim__getArg
||| `getArg`: argument `n` of the program, its name argument 0, its bytes as
||| the system gave them; the empty string for an `n` it has no argument for.
export covering
prim__getArg : Int -> PrimIO (Flat.Uniform String)
prim__getArg n w = let (Runtime.MkHeap # r) = argOp Runtime.MkHeap in MkIORes r w
  where
    -- the bytes up to the zero byte that ends them
    covering
    zeroAt : Runtime.Raw -> Bits64 -> Runtime.Heap.Op Runtime.Heap Bits64
    zeroAt p i = do
      b <- Runtime.Memory.loadByteAt p i
      if b == 0 then Runtime.Heap.pure i else zeroAt p (i + 1)

    -- the bytes copied, and the OR of them, whose top bit says whether any
    -- is not ASCII
    covering
    copy : Runtime.Raw -> Obj Types.Kind.STRING -> (i, end, seen : Bits64) -> Runtime.Heap.Op Runtime.Heap Bits64
    copy p s i end seen = if i >= end then Runtime.Heap.pure seen else do
      b <- Runtime.Memory.loadByteAt p i
      setByte s i b
      copy p s (i + 1) end (seen .|. b)

    covering
    argOp : Runtime.Heap.Op Runtime.Heap (Flat.Uniform String)
    argOp = do
      count <- Runtime.Memory.argumentCount
      if n < 0 || cast n >= count
         then do
           s <- newString 0
           finish s True 0
         else do
           p <- Runtime.Memory.argumentBytes (cast n)
           len <- zeroAt p 0
           s <- newString len
           seen <- copy p s 0 len 0
           finish s (seen < 0x80) len

------------------------------------------------------------------------------
-- Text as numbers

||| What a decimal's digits are, as a scan from its first digit finds them:
||| the byte after them, how many digits there are, how many before the
||| point, how many zeros lead the first nonzero one, how many are from it
||| on, the first 19 of those as a word, and whether there was a point.
record Scan where
  constructor MkScan
  end, digits, whole, lead, significant, w : Bits64
  point : Bool

%cg native flat Support.String.Utf8.readWord
||| The integer a string is, modulo 2^64, which each cast from a string to an
||| integer type wraps to its width, as Idris's casts from `Integer` wrap.
||| Idris does not say what text these casts read, and its code generators'
||| read different texts, so this reads the text every one of them reads: a
||| sign, `+` or `-`, digits with at most one point among them and at least
||| one digit; its value the decimal's, truncated toward zero (12.7 is 12,
||| -12.7 is -12). Any other text is 0, what each gives for the empty string.
|||
||| Chez reads more, any number of its own (1e3 as 1000, 1/2 as 0), and reads
||| a decimal with a point as a double first, losing its digits beyond the
||| 17th; C's `atoi`, which Idris's RefC code generator reads every width
||| by, reads 32 bits, and leading spaces and trailing text. Neither is
||| read here: an exponent, a space or any other character is no integer.
export covering
readWord : Runtime.PortTy Runtime.Memory.Addr (Types.StringRoutine.port Types.StringRoutine.ReadWord)
readWord u = do
  s <- stringObject u
  h <- headerOf s
  let n = bytesOf h
  if n == 0 then Runtime.Heap.pure 0 else do
    c0 <- byteAt s 0
    let negative = c0 == 45
    digits s n (if negative || c0 == 43 then 1 else 0) 0 False False negative
  where
    -- the digits from byte `i`, the whole part's value `v` so far, modulo
    -- 2^64; the fraction's digits are read and dropped
    covering
    digits : Obj Types.Kind.STRING -> (n, i, v : Bits64) -> (any, point, negative : Bool) -> Runtime.Heap.Op Runtime.Heap Bits64
    digits s n i v any point negative =
      if i >= n then Runtime.Heap.pure (if not any then 0 else if negative then 0 - v else v) else do
        b <- byteAt s i
        if b == 46 && not point
           then digits s n (i + 1) v any True negative
           else if b >= 48 && b <= 57
             then digits s n (i + 1) (if point then v else v * 10 + (b - 48)) True point negative
             else Runtime.Heap.pure 0

%cg native flat Support.String.Utf8.readDouble
||| The double a string is. Idris does not say what text its cast reads,
||| and its code generators' casts read different texts (Chez's
||| `string->number`, C's `strtod`, JavaScript's `Number`), so this reads
||| the text every one of them reads, as IEEE 754 reads a decimal, and the
||| text `showDouble` writes, so that a double reads back as itself:
|||
||| * a decimal: a sign, `+` or `-`, digits with at most one point among
|||   them and at least one digit, and an exponent, `e` or `E`, a sign and
|||   digits; rounded to the nearest double, ties to even, its sign kept,
|||   -0 as -0.0;
||| * `+inf.0`, `-inf.0` and `+nan.0`, as `showDouble` writes them.
|||
||| Any other text is 0.0, what each code generator gives for the empty
||| string. Chez reads more: R6RS's exponent markers s, f, d and l, a
||| mantissa width (`1.5|53`), ratios (`1/2`), `-nan.0`; and reads -0, an
||| exact integer there, as 0.0. None of those is the others', and this
||| reads none of them.
|||
||| A decimal of at most 19 significant digits is rounded by them alone
||| (`Nearest.nearest`); a longer one by its first 19, unless those and the
||| 19 raised by one round to two doubles, where it is decided exactly
||| (`Between.between`).
export covering
readDouble : Runtime.PortTy Runtime.Memory.Addr (Types.StringRoutine.port Types.StringRoutine.ReadDouble)
readDouble u = do
  s <- stringObject u
  h <- headerOf s
  let n = bytesOf h
  if n == 0 then Runtime.Heap.pure 0.0 else do
    c0 <- byteAt s 0
    let negative = c0 == 45
        signed = negative || c0 == 43
        i0 : Bits64 = if signed then 1 else 0
        sign : Bits64 = if negative then 0x8000000000000000 else 0
    special <- if signed && n == 6 then word5 s 1 else Runtime.Heap.pure 0
    -- inf.0 after a sign, nan.0 after a plus
    if special == 0x302E666E69
       then Runtime.Heap.pure (bitsDouble (sign .|. 0x7FF0000000000000))
       else if special == 0x302E6E616E && not negative
         then Runtime.Heap.pure (bitsDouble 0x7FF8000000000000)
         else decimalValue s n i0 sign
  where
    ||| What `exponent` gives for a marker without digits after it.
    badExponent : Int
    badExponent = 0x7FFFFFFF

    ||| Five bytes from `i`, the first lowest.
    covering
    word5 : Obj Types.Kind.STRING -> Bits64 -> Runtime.Heap.Op Runtime.Heap Bits64
    word5 s i = do
      b0 <- byteAt s i
      b1 <- byteAt s (i + 1)
      b2 <- byteAt s (i + 2)
      b3 <- byteAt s (i + 3)
      b4 <- byteAt s (i + 4)
      Runtime.Heap.pure (b0 .|. (b1 `shiftL` 8) .|. (b2 `shiftL` 16) .|. (b3 `shiftL` 24) .|. (b4 `shiftL` 32))

    ||| The decimal digits of a number from byte `i` to the first that is no
    ||| digit: whether there is one, the value, at most 100000, past which any
    ||| exponent is as good, and the byte after them.
    covering
    scanNumber : Obj Types.Kind.STRING -> (n, i : Bits64) -> Runtime.Heap.Op Runtime.Heap (Bool, Int, Bits64)
    scanNumber s n i = go i False 0
      where
        covering
        go : Bits64 -> Bool -> Int -> Runtime.Heap.Op Runtime.Heap (Bool, Int, Bits64)
        go j any v = if j >= n then Runtime.Heap.pure (any, v, j) else do
          b <- byteAt s j
          if b < 48 || b > 57
             then Runtime.Heap.pure (any, v, j)
             else go (j + 1) True (if v >= 100000 then v else v * 10 + cast (b - 48))

    ||| An exponent at byte `i`: whether there is a marker, the exponent
    ||| (`badExponent` if no digit follows the marker and its sign), and the
    ||| byte after it.
    covering
    exponent : Obj Types.Kind.STRING -> (n, i : Bits64) -> Runtime.Heap.Op Runtime.Heap (Bool, Int, Bits64)
    exponent s n i = if i >= n then Runtime.Heap.pure (False, 0, i) else do
      b <- byteAt s i
      -- e or E
      if b /= 101 && b /= 69
         then Runtime.Heap.pure (False, 0, i)
         else do
           c <- if i + 1 < n then byteAt s (i + 1) else Runtime.Heap.pure 0
           let minus = c == 45
               start = if minus || c == 43 then i + 2 else i + 1
           (any, v, j) <- scanNumber s n start
           Runtime.Heap.pure (True, if not any then badExponent else if minus then negate v else v, j)

    ||| The digits from byte `i`, with at most one point among them.
    covering
    scanDigits : Obj Types.Kind.STRING -> (n, i : Bits64) -> Scan -> Runtime.Heap.Op Runtime.Heap Scan
    scanDigits s n i (MkScan end digits whole lead sig w point) =
      if i >= n then Runtime.Heap.pure (MkScan end digits whole lead sig w point) else do
        b <- byteAt s i
        if b == 46 && not point
           then scanDigits s n (i + 1) (MkScan (i + 1) digits whole lead sig w True)
           else if b < 48 || b > 57
             then Runtime.Heap.pure (MkScan end digits whole lead sig w point)
             else
               let d = b - 48
                   whole' = if point then whole else whole + 1
               in if sig == 0 && d == 0
                     then scanDigits s n (i + 1) (MkScan (i + 1) (digits + 1) whole' (lead + 1) sig w point)
                     else scanDigits s n (i + 1)
                            (MkScan (i + 1) (digits + 1) whole' lead (sig + 1) (if sig < 19 then w * 10 + d else w) point)

    ||| The digits of a decimal as a number in limbs, from its first nonzero
    ||| one, at most `most` of them, and whether a nonzero digit follows those.
    covering
    gatherDigits : Obj Types.Kind.STRING -> (from, end, lead, most : Bits64) -> Limbs -> Runtime.Heap.Op Runtime.Heap Bool
    gatherDigits s from end lead most d = go from lead 0 0 0 False
      where
        -- the digits are taken 19 at a time into a word, each word then added
        -- in times 10 to the power of its digits
        covering
        flush : (chunk, digits : Bits64) -> Runtime.Heap.Op Runtime.Heap ()
        flush chunk 0 = Runtime.Heap.pure ()
        flush chunk digits = mulAdd d (power digits) chunk
          where
            power : Bits64 -> Bits64
            power 0 = 1
            -- lint: allow trust-escape: j is positive here, so j - 1 is smaller
            power j = 10 * power (assert_smaller j (j - 1))

        covering
        go : (i, skip, taken, chunk, inChunk : Bits64) -> (sticky : Bool) -> Runtime.Heap.Op Runtime.Heap Bool
        go i skip taken chunk inChunk sticky =
          if i >= end then do flush chunk inChunk; Runtime.Heap.pure sticky else do
            b <- byteAt s i
            let v = b - 48
            if b == 46
               then go (i + 1) skip taken chunk inChunk sticky
               else if skip > 0
                 then go (i + 1) (skip - 1) taken chunk inChunk sticky
                 else if taken >= most
                   then go (i + 1) 0 taken chunk inChunk (sticky || v /= 0)
                   else if inChunk == 19
                     then do
                       flush chunk inChunk
                       go (i + 1) 0 (taken + 1) v 1 sticky
                     else go (i + 1) 0 (taken + 1) (chunk * 10 + v) (inChunk + 1) sticky

    ||| A decimal from byte `i0`, its sign's bit `sign`.
    covering
    decimalValue : Obj Types.Kind.STRING -> (n, i0, sign : Bits64) -> Runtime.Heap.Op Runtime.Heap Double
    decimalValue s n i0 sign = do
      sc <- scanDigits s n i0 (MkScan i0 0 0 0 0 0 False)
      (hasExponent, e, j) <- exponent s n sc.end
      let invalid = sc.digits == 0 || j /= n || (hasExponent && e == badExponent)
      if invalid then Runtime.Heap.pure 0.0 else
        if sc.significant == 0
           then Runtime.Heap.pure (bitsDouble sign)
           else do
             let k = if sc.significant > 19 then 19 else sc.significant
                 q = e + cast sc.whole - cast sc.lead - cast k
                 b = nearest sc.w q
             bits <- if sc.significant <= 19 || b == nearest (sc.w + 1) q
                        then Runtime.Heap.pure b
                        else do
                          d <- newLimbs
                          sticky <- gatherDigits s i0 sc.end sc.lead 769 d
                          let kept = if sc.significant > 769 then 769 else sc.significant
                          between d sticky (e + cast sc.whole - cast sc.lead - cast kept) b
             Runtime.Heap.pure (bitsDouble (bits .|. sign))
