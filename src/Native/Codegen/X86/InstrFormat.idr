||| An x86-64 instruction's bytes as Intel's instruction format describes
||| them (`InstrFormat`): the parts the instruction has, in the order they
||| are written, each a number of a fixed width. The encoder
||| (`Native.Codegen.X86.Encode`) gives an instruction's; it is read three
||| ways here: the bytes it takes (`size`), with no byte made; its bytes
||| (`bytes`); and its bytes written, part by part, through a span over
||| the bytes it takes (`write`), whose type makes the parts' widths sum to
||| its size, into a sink with one check (`put`).
module Native.Codegen.X86.InstrFormat

import Native.Codegen.X86.OptionalByte

import Data.List
import Native.Codegen.LittleEndian
import Native.Data.ByteSink as Data

%default total

------------------------------------------------------------------------------
-- The parts

||| The opcode map an opcode is of: Intel's one-byte map, or its two-byte
||| map, whose opcodes are escaped by the byte 0x0F before them.
public export
data OpcodeMap = OneByte | TwoByte

namespace OpcodeMap
  ||| The bytes the map's escape takes.
  export
  size : OpcodeMap -> Nat
  size OneByte = 0
  size TwoByte = 1

  ||| The map's escape.
  export
  bytes : OpcodeMap -> List Bits8
  bytes OneByte = []
  bytes TwoByte = [0x0F]

  ||| The map's escape written at the span's next byte.
  export
  write : (s : Data.ByteSink) -> (m : OpcodeMap) -> Data.ByteSink.Span s (size m + n) ->
          IO (Data.ByteSink.Span s n)
  write s OneByte sp = pure sp
  write s TwoByte sp = Data.ByteSink.putBits8 s sp 0x0F

||| The width of a displacement: none, 8 bits or 32.
public export
data DispWidth = NoDisp | Disp8 | Disp32

namespace DispWidth
  ||| The bytes a displacement of the width takes.
  export
  size : DispWidth -> Nat
  size NoDisp = 0
  size Disp8 = 1
  size Disp32 = 4

  ||| A displacement's bytes at the width: its low bits, as two's
  ||| complement, low byte first.
  export
  bytes : DispWidth -> Int -> List Bits8
  bytes NoDisp _ = []
  bytes Disp8 d = LittleEndian.le8 d
  bytes Disp32 d = LittleEndian.le32 d

  ||| A displacement's bytes at the width written at the span's next byte.
  export
  write : (s : Data.ByteSink) -> (dw : DispWidth) -> Int -> Data.ByteSink.Span s (size dw + n) ->
          IO (Data.ByteSink.Span s n)
  write s NoDisp _ sp = pure sp
  write s Disp8 d sp = Data.ByteSink.putBits8 s sp (cast d)
  write s Disp32 d sp = Data.ByteSink.putBits32 s sp (cast d)

||| The width of an immediate: none, 8 bits, 32 or 64.
public export
data ImmWidth = NoImm | Imm8 | Imm32 | Imm64

namespace ImmWidth
  ||| The bytes an immediate of the width takes.
  export
  size : ImmWidth -> Nat
  size NoImm = 0
  size Imm8 = 1
  size Imm32 = 4
  size Imm64 = 8

  ||| An immediate's bytes at the width: its low bits, as two's complement,
  ||| low byte first.
  export
  bytes : ImmWidth -> Int -> List Bits8
  bytes NoImm _ = []
  bytes Imm8 i = LittleEndian.le8 i
  bytes Imm32 i = LittleEndian.le32 i
  bytes Imm64 i = LittleEndian.le64 (cast i)

  ||| An immediate's bytes at the width written at the span's next byte.
  export
  write : (s : Data.ByteSink) -> (iw : ImmWidth) -> Int -> Data.ByteSink.Span s (size iw + n) ->
          IO (Data.ByteSink.Span s n)
  write s NoImm _ sp = pure sp
  write s Imm8 i sp = Data.ByteSink.putBits8 s sp (cast i)
  write s Imm32 i sp = Data.ByteSink.putBits32 s sp (cast i)
  write s Imm64 i sp = Data.ByteSink.putBits64 s sp (cast i)

------------------------------------------------------------------------------
-- An instruction's bytes

||| An instruction's bytes as Intel's instruction format lays them out, or
||| the bytes of a directive of the assembler.
public export
data InstrFormat : Type where
  ||| An instruction: its parts, in the order they are written. A legacy
  ||| prefix (0x66, 0xF2 or 0xF0) and a REX prefix, each if it has one;
  ||| its opcode, of the map given; a ModRM byte and a SIB byte, each if it
  ||| has one; a displacement and an immediate, each the low bits of its
  ||| number that its width says, none for no width. A branch's offset
  ||| from the end of the instruction (rel32) is its immediate, the one
  ||| part after its opcode.
  Parts : (legacy, rex : OptionalByte) -> (opcodeMap : OpcodeMap) -> (opcode : Bits8) ->
          (modrm, sib : OptionalByte) -> (dispWidth : DispWidth) -> (disp : Int) ->
          (immWidth : ImmWidth) -> (imm : Int) -> InstrFormat
  ||| So many bytes of `int3` (0xCC): padding to an alignment, never run.
  Padding : (n : Nat) -> InstrFormat
  ||| A word: its eight bytes, low byte first.
  Literal : Bits64 -> InstrFormat
  ||| These bytes, as they are; none for a label or a comment.
  Verbatim : List Bits8 -> InstrFormat

||| The bytes an instruction takes: its parts' sizes summed, with no byte
||| made. Each sum is of a part and the parts after it, ending in 0 for
||| none, as the parts are written (`write`), each taking its own from the
||| front.
export
size : InstrFormat -> Nat
-- a `Nat`, the index of the span the instruction is written through
size (Parts p r m _ modrm sib dw _ iw _) =
  OptionalByte.size p + (OptionalByte.size r + (OpcodeMap.size m + (1 + (OptionalByte.size modrm
    + (OptionalByte.size sib + (DispWidth.size dw + (ImmWidth.size iw + 0)))))))
size (Padding n) = n + 0
size (Literal _) = 8
size (Verbatim bs) = length bs + 0

||| The bytes before an instruction's displacement, where it is; where its
||| immediate is, if it has no displacement; 0 for a directive.
export
dispAt : InstrFormat -> Nat
dispAt (Parts p r m _ modrm sib _ _ _ _) =
  OptionalByte.size p + OptionalByte.size r + OpcodeMap.size m + 1 + OptionalByte.size modrm
    + OptionalByte.size sib
dispAt _ = 0

||| An instruction's bytes, in order.
export
bytes : InstrFormat -> List Bits8
bytes (Parts p r m o modrm sib dw d iw i) =
  OptionalByte.bytes p ++ OptionalByte.bytes r ++ OpcodeMap.bytes m ++ [o]
    ++ OptionalByte.bytes modrm ++ OptionalByte.bytes sib ++ DispWidth.bytes dw d
    ++ ImmWidth.bytes iw i
bytes (Padding n) = replicate n 0xCC
bytes (Literal v) = LittleEndian.le64 (cast v)
bytes (Verbatim bs) = bs

||| An instruction's bytes written through a span over the bytes it takes,
||| part by part, each from the front of what is left, to its end.
export
write : (s : Data.ByteSink) -> (f : InstrFormat) -> Data.ByteSink.Span s (size f) ->
        IO (Data.ByteSink.Span s 0)
write s (Parts p r m o modrm sib dw d iw i) sp = do
  sp <- OptionalByte.write s p sp
  sp <- OptionalByte.write s r sp
  sp <- OpcodeMap.write s m sp
  sp <- Data.ByteSink.putBits8 s sp o
  sp <- OptionalByte.write s modrm sp
  sp <- OptionalByte.write s sib sp
  sp <- DispWidth.write s dw d sp
  ImmWidth.write s iw i sp
write s (Padding n) sp = Data.ByteSink.putCopies s n 0xCC sp
write s (Literal v) sp = Data.ByteSink.putBits64 s sp v
write s (Verbatim bs) sp = Data.ByteSink.putBytes s bs sp

||| An instruction's bytes written at the sink's next offset, if they fit
||| before the sink's end, with one check (`ByteSink.fits`): one that does
||| not fit writes nothing, and gives no sink.
export
put : Data.ByteSink -> InstrFormat -> IO (Maybe Data.ByteSink)
put s f with (Data.ByteSink.fits s (Data.ByteSink.start s) (size f)) proof ok
  _ | True = do
    end <- write s f (Data.ByteSink.span s (Data.ByteSink.start s) _ ok)
    pure (Just (Data.ByteSink.past s end))
  _ | False = pure Nothing
