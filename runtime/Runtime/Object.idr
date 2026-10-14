||| Objects as the collector reads them: words. An object's first word is
||| its header, or, for a continuation, the address of the code that resumes
||| it; from that word the collector learns the object's kind, its size and
||| which of its words hold values it must follow. These are the rules of
||| `Compiler.Native.HeapObject.Header`, restated over words for code that cannot
||| hold a `Header`; the test `object001` keeps the two in step.
module Runtime.Object

-- lint: allow public-import: the flat translation reaches through this module
-- (checking an importer's flat functions, it reaches this module's bodies,
-- which use it, so it is loaded wherever this module is)
import public Compiler.Native.HeapObject.Header

import Compiler.Native.HeapObject.Kind
import Runtime.Bits

%default total

||| The low four bits of a header word: the kind's id, or 0 for a
||| continuation, whose first word is a 16-aligned code address.
export
kindOfHeader : Bits64 -> Bits64
kindOfHeader h = h .&. 15

export
isContinuation : (header : Bits64) -> Bool
isContinuation h = kindOfHeader h == 0

||| The forwarding header, which a collector writes over the first word of
||| an object it has moved: kind 15, and the new address, 8-aligned, in the
||| rest of the word.
export
forwardingId : Bits64
forwardingId = 15

export
forwardingHeader : (to : Bits64) -> Bits64
forwardingHeader to = shiftL to 4 .|. forwardingId

export
forwardedTo : (header : Bits64) -> Bits64
forwardedTo h = shiftR h 4

||| A part of a header word, where `place` puts it. Inline, so that at a
||| part written in the code the shift and the mask are constants.
export %inline
part : HeaderPart k -> (header : Bits64) -> Bits64
part p h = shiftR h (fst (place p)) .&. (shiftL 1 (snd (place p)) - 1)

||| The words `bytes` take, rounded up.
export %inline
byteWords : Bits64 -> Bits64
byteWords b = shiftR (b + 7) 3

||| The words of an object with a header, the header included, by its kind's
||| id and its header word; 0 for an id that is no kind's.
export
objectWords : (id, header : Bits64) -> Bits64
objectWords id h =
  if id == kindId CON then 1 + part ConArity h
  else if id == kindId CLOSURE then 2 + part ClosureFilled h
  else if id == kindId INT64 then 2
  else if id == kindId DOUBLE then 2
  else if id == kindId STRING then 1 + byteWords (part StringBytes h)
  else if id == kindId BIGNUM then 1 + part BignumWords h
  else if id == kindId IOREF then 2
  else if id == kindId ARRAY then 1 + part ArrayElems h
  else if id == kindId BUFFER then 1 + byteWords (part BufferBytes h)
  else if id == kindId PTR then 2
  else 0

||| The words of an object with a header that hold values: the first, and
||| how many. Every other word is raw.
export
scannedWords : (id, header : Bits64) -> (Bits64, Bits64)
scannedWords id h =
  if id == kindId CON then (1, part ConArity h)
  else if id == kindId CLOSURE then (2, part ClosureFilled h)
  else if id == kindId IOREF then (1, 1)
  else if id == kindId ARRAY then (1, part ArrayElems h)
  else (1, 0)

||| A continuation's layout word, the word before the code that resumes
||| it: the live values in bits 0 to 23, the live raw words in bits 24 to
||| 47. The continuation holds the code's address, its parent, the values,
||| then the raw words.
export
layoutValues : (layout : Bits64) -> Bits64
layoutValues l = l .&. 0xFFFFFF

export
layoutRaws : (layout : Bits64) -> Bits64
layoutRaws l = shiftR l 24 .&. 0xFFFFFF

export
continuationWords : (layout : Bits64) -> Bits64
continuationWords l = 2 + layoutValues l + layoutRaws l

||| The words of a continuation that hold values: its parent and the live
||| values.
export
continuationScanned : (layout : Bits64) -> (Bits64, Bits64)
continuationScanned l = (1, 1 + layoutValues l)
