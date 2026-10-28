||| An x86-64 instruction's bytes as Intel's instruction format describes
||| them (`InstrFormat`): the parts the instruction has, in the order they
||| are written, each a number of a fixed width. The encoder
||| (`Native.Codegen.X86.Encode`) gives an instruction's; it is read three
||| ways here: the bytes it takes (`size`), with no byte made; its bytes
||| (`bytes`); and its bytes written through a sink
||| (`Native.Codegen.ByteSink`), part by part (`put`).
module Native.Codegen.X86.InstrFormat

import Native.Codegen.X86.OptionalByte

import Data.List
import Native.Codegen.ByteSink
import Native.Codegen.LittleEndian

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

  ||| The map's escape written.
  export
  put : ByteSink.Sink -> OpcodeMap -> IO (Maybe ByteSink.Sink)
  put s OneByte = pure (Just s)
  put s TwoByte = ByteSink.putBits8 s 0x0F

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

  ||| A displacement's bytes at the width written.
  export
  put : ByteSink.Sink -> DispWidth -> Int -> IO (Maybe ByteSink.Sink)
  put s NoDisp _ = pure (Just s)
  put s Disp8 d = ByteSink.putBits8 s (cast d)
  put s Disp32 d = ByteSink.putBits32 s (cast d)

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

  ||| An immediate's bytes at the width written.
  export
  put : ByteSink.Sink -> ImmWidth -> Int -> IO (Maybe ByteSink.Sink)
  put s NoImm _ = pure (Just s)
  put s Imm8 i = ByteSink.putBits8 s (cast i)
  put s Imm32 i = ByteSink.putBits32 s (cast i)
  put s Imm64 i = ByteSink.putBits64 s (cast i)

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
||| made.
export
size : InstrFormat -> Int
-- the parts' sizes summed as `Nat`s, which Idris's Chez code adds as
-- Scheme adds, where it wraps each sum of two `Int`s to 64 bits, at
-- several times the cost
size (Parts p r m _ modrm sib dw _ iw _) = cast $
  OptionalByte.size p + OptionalByte.size r + OpcodeMap.size m + 1 + OptionalByte.size modrm
    + OptionalByte.size sib + DispWidth.size dw + ImmWidth.size iw
size (Padding n) = cast n
size (Literal _) = 8
size (Verbatim bs) = cast (length bs)

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

||| An instruction's bytes written at the sink's next offset, part by part,
||| each if it fits before the sink's end: one that does not fit is
||| written up to the first part that does not, and gives no sink.
export
put : ByteSink.Sink -> InstrFormat -> IO (Maybe ByteSink.Sink)
-- a `case` whose every branch is an action, as each write of a sink is
put s f = case f of
  Parts p r m o modrm sib dw d iw i => do
    Just s <- OptionalByte.put s p
      | Nothing => pure Nothing
    Just s <- OptionalByte.put s r
      | Nothing => pure Nothing
    Just s <- OpcodeMap.put s m
      | Nothing => pure Nothing
    Just s <- ByteSink.putBits8 s o
      | Nothing => pure Nothing
    Just s <- OptionalByte.put s modrm
      | Nothing => pure Nothing
    Just s <- OptionalByte.put s sib
      | Nothing => pure Nothing
    Just s <- DispWidth.put s dw d
      | Nothing => pure Nothing
    ImmWidth.put s iw i
  Padding n => ByteSink.put s (replicate n 0xCC)
  Literal v => ByteSink.putBits64 s v
  Verbatim bs => ByteSink.put s bs
