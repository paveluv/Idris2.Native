||| Code points as UTF-8 (`utf8Bytes`, `encodeUtf8`, `decodeUtf8`): how many
||| bytes a code point takes, shortest form, and writing and reading one in
||| memory, at an address plus an offset. The bytes of a string under UTF-8
||| are these, and so are those of the console and of files, whatever the
||| program's string encoding.
module Native.Support.CodePoint

-- lint: allow public-import: the flat translation reaches through this module
-- (checking an importer's flat functions, it reaches the bodies here, which
-- use the bit operations, so it is loaded wherever this module is)
import public Native.Runtime.Bits

import Native.Support.Obj

import Native.Heap
import Native.Types.Kind as Types

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| The bytes of the code point `c`, shortest form.
export
utf8Bytes : (c : Bits64) -> Bits64
utf8Bytes c = if c < 0x80 then 1 else if c < 0x800 then 2 else if c < 0x10000 then 3 else 4

||| The bytes of the code point whose lead byte is `b`.
export
utf8Length : (lead : Bits64) -> Bits64
utf8Length b = if b < 0x80 then 1 else if b < 0xE0 then 2 else if b < 0xF0 then 3 else 4

||| The code point whose lead byte is at the address plus the offset, the
||| bytes after it its sequence's, trusted to be well formed.
export
decodeUtf8 : Obj k -> (offset : Bits64) -> Heap.Op Heap Bits64
decodeUtf8 a i = do
  b0 <- Obj.load8 a i
  if b0 < 0x80 then Heap.pure b0 else
    if b0 < 0xE0 then do
      b1 <- Obj.load8 a (i + 1)
      Heap.pure (Runtime.Bits.shiftL (b0 .&. 0x1F) 6 .|. b1 .&. 0x3F)
    else if b0 < 0xF0 then do
      b1 <- Obj.load8 a (i + 1)
      b2 <- Obj.load8 a (i + 2)
      Heap.pure (Runtime.Bits.shiftL (b0 .&. 0x0F) 12 .|. Runtime.Bits.shiftL (b1 .&. 0x3F) 6 .|. b2 .&. 0x3F)
    else do
      b1 <- Obj.load8 a (i + 1)
      b2 <- Obj.load8 a (i + 2)
      b3 <- Obj.load8 a (i + 3)
      Heap.pure (Runtime.Bits.shiftL (b0 .&. 0x07) 18 .|. Runtime.Bits.shiftL (b1 .&. 0x3F) 12
            .|. Runtime.Bits.shiftL (b2 .&. 0x3F) 6 .|. b3 .&. 0x3F)

||| The bytes of the code point `c`, its `utf8Bytes c` of them, in one word,
||| the first lowest, as memory holds them on a little-endian machine.
export
utf8Word : (c : Bits64) -> Bits64
utf8Word c =
  if c < 0x80 then c
  else if c < 0x800 then
    (0xC0 .|. Runtime.Bits.shiftR c 6) .|. Runtime.Bits.shiftL (0x80 .|. c .&. 0x3F) 8
  else if c < 0x10000 then
    (0xE0 .|. Runtime.Bits.shiftR c 12) .|. Runtime.Bits.shiftL (0x80 .|. Runtime.Bits.shiftR c 6 .&. 0x3F) 8
      .|. Runtime.Bits.shiftL (0x80 .|. c .&. 0x3F) 16
  else
    (0xF0 .|. Runtime.Bits.shiftR c 18) .|. Runtime.Bits.shiftL (0x80 .|. Runtime.Bits.shiftR c 12 .&. 0x3F) 8
      .|. Runtime.Bits.shiftL (0x80 .|. Runtime.Bits.shiftR c 6 .&. 0x3F) 16 .|. Runtime.Bits.shiftL (0x80 .|. c .&. 0x3F) 24

||| The code point `c` written at the address plus the offset, its
||| `utf8Bytes c` bytes.
export
encodeUtf8 : Obj k -> (offset, c : Bits64) -> Heap.Op Heap ()
encodeUtf8 a j c =
  let w = utf8Word c in
  if c < 0x80 then Obj.store8 a j w
  else if c < 0x800 then Obj.store16 a j w
  else if c < 0x10000 then do
    Obj.store16 a j w
    Obj.store8 a (j + 2) (Runtime.Bits.shiftR w 16)
  else Obj.store32 a j w
