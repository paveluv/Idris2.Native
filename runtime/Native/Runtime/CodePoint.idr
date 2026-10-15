||| Code points as UTF-8 (`utf8Bytes`, `encodeUtf8`, `decodeUtf8`): how many
||| bytes a code point takes, shortest form, and writing and reading one in
||| memory, at an address plus an offset. The bytes of a string under UTF-8
||| are these, and so are those of the console and of files, whatever the
||| program's string encoding.
module Native.Runtime.CodePoint

-- lint: allow public-import: the flat translation reaches through this module
-- (checking an importer's flat functions, it reaches the bodies here, which
-- use the bit operations, so it is loaded wherever this module is)
import public Native.Runtime.Bits

import Native.Runtime.Memory

import Native.Heap
import Native.HeapObj.Kind

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
decodeUtf8 : Memory.Addr k -> (offset : Bits64) -> Heap.Op Heap Bits64
decodeUtf8 a i = do
  b0 <- Memory.load8 a i
  if b0 < 0x80 then Heap.pure b0 else
    if b0 < 0xE0 then do
      b1 <- Memory.load8 a (i + 1)
      Heap.pure (Bits.shiftL (b0 .&. 0x1F) 6 .|. b1 .&. 0x3F)
    else if b0 < 0xF0 then do
      b1 <- Memory.load8 a (i + 1)
      b2 <- Memory.load8 a (i + 2)
      Heap.pure (Bits.shiftL (b0 .&. 0x0F) 12 .|. Bits.shiftL (b1 .&. 0x3F) 6 .|. b2 .&. 0x3F)
    else do
      b1 <- Memory.load8 a (i + 1)
      b2 <- Memory.load8 a (i + 2)
      b3 <- Memory.load8 a (i + 3)
      Heap.pure (Bits.shiftL (b0 .&. 0x07) 18 .|. Bits.shiftL (b1 .&. 0x3F) 12
            .|. Bits.shiftL (b2 .&. 0x3F) 6 .|. b3 .&. 0x3F)

||| The code point `c` written at the address plus the offset, its
||| `utf8Bytes c` bytes.
export
encodeUtf8 : Memory.Addr k -> (offset, c : Bits64) -> Heap.Op Heap ()
encodeUtf8 a j c =
  if c < 0x80 then Memory.store8 a j c
  else if c < 0x800 then do
    Memory.store8 a j (0xC0 .|. Bits.shiftR c 6)
    Memory.store8 a (j + 1) (0x80 .|. c .&. 0x3F)
  else if c < 0x10000 then do
    Memory.store8 a j (0xE0 .|. Bits.shiftR c 12)
    Memory.store8 a (j + 1) (0x80 .|. Bits.shiftR c 6 .&. 0x3F)
    Memory.store8 a (j + 2) (0x80 .|. c .&. 0x3F)
  else do
    Memory.store8 a j (0xF0 .|. Bits.shiftR c 18)
    Memory.store8 a (j + 1) (0x80 .|. Bits.shiftR c 12 .&. 0x3F)
    Memory.store8 a (j + 2) (0x80 .|. Bits.shiftR c 6 .&. 0x3F)
    Memory.store8 a (j + 3) (0x80 .|. c .&. 0x3F)
