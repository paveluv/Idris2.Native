||| x86-64 encoder and two-pass assembler.
|||
||| `instrFormat` is the encoder: a pure function from an instruction (with
||| any label-relative displacement already computed) to its parts in
||| Intel's instruction format (`Native.Codegen.X86.InstrFormat`), total
||| over `Instr`, and the one place the rules of an instruction's bytes
||| are; `encodeRaw` is its bytes, `instrSize` the bytes it takes. Two
||| facts of those rules are stated apart, each once: the bits a field's
||| value must fit (`fieldsFit`), and the instructions that refer to a
||| label, by a displacement from their end (`instrLabel`). `assemble`
||| lays out a code stream: pass one assigns label addresses (every
||| instruction's size is independent of label values because branches
||| and RIP-relative operands always use rel32), pass two encodes with
||| resolved displacements. Alignment padding is `int3`, never executed.
module Native.Codegen.X86.Encode

import Native.Codegen.X86.Asm
import Native.Codegen.X86.InstrFormat
import Native.Codegen.X86.LabelTable
import Native.Codegen.X86.OptionalByte

import Data.Bits
import Data.Buffer
import Native.Codegen.ByteSink
%default total

------------------------------------------------------------------------------
-- Immediates

||| Whether the number fits 32 bits, signed.
fitsInt32 : Integer -> Bool
fitsInt32 x = x >= -2147483648 && x <= 2147483647

------------------------------------------------------------------------------
-- The encoder

||| An instruction's parts, in Intel's instruction format, with any
||| label-relative displacement already resolved to `rel`. For `Align`,
||| `pc` is the address of the instruction.
export
instrFormat : (pc, rel : Int) -> Asm.Instr -> InstrFormat
instrFormat pc rel instr = case instr of
  Asm.MovRR d s => regForm 0 True 0x89 (Asm.regNum s) (Asm.regNum d) False InstrFormat.NoImm 0
  Asm.MovRI d i => movImmForm (Asm.regNum d) i
  Asm.MovRM d m => memForm 0 True 0x8B (Asm.regNum d) m False InstrFormat.NoImm 0
  Asm.MovMR m s => memForm 0 True 0x89 (Asm.regNum s) m False InstrFormat.NoImm 0
  Asm.MovMI m i => memForm 0 True 0xC7 0 m False InstrFormat.Imm32 i
  Asm.Lea d m => memForm 0 True 0x8D (Asm.regNum d) m False InstrFormat.NoImm 0
  Asm.Load Asm.W8 False d m => memForm 0 True 0x0FB6 (Asm.regNum d) m False InstrFormat.NoImm 0
  Asm.Load Asm.W8 True d m => memForm 0 True 0x0FBE (Asm.regNum d) m False InstrFormat.NoImm 0
  Asm.Load Asm.W16 False d m => memForm 0 True 0x0FB7 (Asm.regNum d) m False InstrFormat.NoImm 0
  Asm.Load Asm.W16 True d m => memForm 0 True 0x0FBF (Asm.regNum d) m False InstrFormat.NoImm 0
  Asm.Load Asm.W32 False d m => memForm 0 False 0x8B (Asm.regNum d) m False InstrFormat.NoImm 0
  Asm.Load Asm.W32 True d m => memForm 0 True 0x63 (Asm.regNum d) m False InstrFormat.NoImm 0
  Asm.Store Asm.W8 m s =>
    memForm 0 False 0x88 (Asm.regNum s) m (byteRegNeedsRex s) InstrFormat.NoImm 0
  Asm.Store Asm.W16 m s => memForm 0x66 False 0x89 (Asm.regNum s) m False InstrFormat.NoImm 0
  Asm.Store Asm.W32 m s => memForm 0 False 0x89 (Asm.regNum s) m False InstrFormat.NoImm 0
  Asm.Alu op d s =>
    regForm 0 True (0x01 + 8 * cast (Asm.aluDigit op)) (Asm.regNum s) (Asm.regNum d) False
      InstrFormat.NoImm 0
  Asm.AluI op d i => immForm 0x83 0x81 (Asm.aluDigit op) (Asm.regNum d) i
  Asm.AluRM op d m =>
    memForm 0 True (0x03 + 8 * cast (Asm.aluDigit op)) (Asm.regNum d) m False InstrFormat.NoImm 0
  Asm.AluMR op m s =>
    memForm 0 True (0x01 + 8 * cast (Asm.aluDigit op)) (Asm.regNum s) m False InstrFormat.NoImm 0
  Asm.Test a b => regForm 0 True 0x85 (Asm.regNum b) (Asm.regNum a) False InstrFormat.NoImm 0
  Asm.TestI a i => regForm 0 True 0xF7 0 (Asm.regNum a) False InstrFormat.Imm32 i
  Asm.Imul d s => regForm 0 True 0x0FAF (Asm.regNum d) (Asm.regNum s) False InstrFormat.NoImm 0
  Asm.ImulI d s i => immForm 0x6B 0x69 (Asm.regNum d) (Asm.regNum s) i
  Asm.Cqo => opcodeForm (OptionalByte.byte 0x48) 0x99 InstrFormat.NoImm 0
  Asm.Idiv r => regForm 0 True 0xF7 7 (Asm.regNum r) False InstrFormat.NoImm 0
  Asm.DivU r => regForm 0 True 0xF7 6 (Asm.regNum r) False InstrFormat.NoImm 0
  Asm.Mul r => regForm 0 True 0xF7 4 (Asm.regNum r) False InstrFormat.NoImm 0
  Asm.Neg r => regForm 0 True 0xF7 3 (Asm.regNum r) False InstrFormat.NoImm 0
  Asm.Not r => regForm 0 True 0xF7 2 (Asm.regNum r) False InstrFormat.NoImm 0
  Asm.ShiftI op r n =>
    regForm 0 True 0xC1 (Asm.shiftDigit op) (Asm.regNum r) False InstrFormat.Imm8 (cast n)
  Asm.ShiftCl op r =>
    regForm 0 True 0xD3 (Asm.shiftDigit op) (Asm.regNum r) False InstrFormat.NoImm 0
  Asm.Jmp _ => opcodeForm OptionalByte.none 0xE9 InstrFormat.Imm32 rel
  Asm.Jcc c _ => opcodeForm OptionalByte.none (0x0F80 + cast (Asm.condCode c)) InstrFormat.Imm32 rel
  Asm.Call _ => opcodeForm OptionalByte.none 0xE8 InstrFormat.Imm32 rel
  Asm.JmpR r => regForm 0 False 0xFF 4 (Asm.regNum r) False InstrFormat.NoImm 0
  Asm.JmpM m => memForm 0 False 0xFF 4 m False InstrFormat.NoImm 0
  Asm.CallR r => regForm 0 False 0xFF 2 (Asm.regNum r) False InstrFormat.NoImm 0
  Asm.Ret => opcodeForm OptionalByte.none 0xC3 InstrFormat.NoImm 0
  Asm.Push r =>
    opcodeForm (rex False 0 0 (Asm.regNum r) False) (0x50 + cast (lo (Asm.regNum r)))
      InstrFormat.NoImm 0
  Asm.Pop r =>
    opcodeForm (rex False 0 0 (Asm.regNum r) False) (0x58 + cast (lo (Asm.regNum r)))
      InstrFormat.NoImm 0
  Asm.Setcc c r =>
    regForm 0 False (0x0F90 + cast (Asm.condCode c)) 0 (Asm.regNum r) (byteRegNeedsRex r)
      InstrFormat.NoImm 0
  Asm.Cmov c d s =>
    regForm 0 True (0x0F40 + cast (Asm.condCode c)) (Asm.regNum d) (Asm.regNum s) False
      InstrFormat.NoImm 0
  Asm.MovsdRM x m => memForm 0xF2 False 0x0F10 (Asm.xmmNum x) m False InstrFormat.NoImm 0
  Asm.MovsdMR m x => memForm 0xF2 False 0x0F11 (Asm.xmmNum x) m False InstrFormat.NoImm 0
  Asm.MovsdRR d s =>
    regForm 0xF2 False 0x0F10 (Asm.xmmNum d) (Asm.xmmNum s) False InstrFormat.NoImm 0
  Asm.Sse op d s =>
    regForm 0xF2 False (0x0F00 + cast (Asm.sseOpcode op)) (Asm.xmmNum d) (Asm.xmmNum s) False
      InstrFormat.NoImm 0
  Asm.Ucomisd a b =>
    regForm 0x66 False 0x0F2E (Asm.xmmNum a) (Asm.xmmNum b) False InstrFormat.NoImm 0
  Asm.Cvtsi2sd x r =>
    regForm 0xF2 True 0x0F2A (Asm.xmmNum x) (Asm.regNum r) False InstrFormat.NoImm 0
  Asm.Cvttsd2si r x =>
    regForm 0xF2 True 0x0F2C (Asm.regNum r) (Asm.xmmNum x) False InstrFormat.NoImm 0
  Asm.MovqXR x r =>
    regForm 0x66 True 0x0F6E (Asm.xmmNum x) (Asm.regNum r) False InstrFormat.NoImm 0
  Asm.MovqRX r x =>
    regForm 0x66 True 0x0F7E (Asm.xmmNum x) (Asm.regNum r) False InstrFormat.NoImm 0
  Asm.Syscall => opcodeForm OptionalByte.none 0x0F05 InstrFormat.NoImm 0
  Asm.LockCmpxchg m r =>
    memForm 0xF0 True 0x0FB1 (Asm.regNum r) m False InstrFormat.NoImm 0
  Asm.Nop => opcodeForm OptionalByte.none 0x90 InstrFormat.NoImm 0
  Asm.Int3 => opcodeForm OptionalByte.none 0xCC InstrFormat.NoImm 0
  Asm.Lbl _ => InstrFormat.Verbatim []
  Asm.Align n => InstrFormat.Padding (padding pc n)
  Asm.Quad v => InstrFormat.Literal (cast v)
  Asm.Bytes bs => InstrFormat.Verbatim bs
  Asm.Comment _ => InstrFormat.Verbatim []
  where
    -- Each form below takes the legacy prefix as its byte, 0 for none (no
    -- legacy prefix is 0), and the opcode as Intel writes it: a byte of
    -- the one-byte map, or 0x0F and a byte of the two-byte map, as one
    -- 16-bit number (0x0FB6 for 0F B6).

    padding : Int -> Nat -> Nat
    padding at n = let m = cast {to = Int} n in
                   if m <= 1 then 0 else cast ((m - (at `mod` m)) `mod` m)

    ||| Byte-register operands 4..7 (spl, bpl, sil, dil) need a REX to be
    ||| addressed at all.
    byteRegNeedsRex : Asm.Reg64 -> Bool
    byteRegNeedsRex r = Asm.regNum r >= 4 && Asm.regNum r <= 7

    lo : Bits8 -> Bits8            -- low three bits
    lo n = n .&. 7

    ||| REX prefix, or none when no bit is needed. `force` requests a bare
    ||| 0x40 (needed to address spl/bpl/sil/dil as byte registers).
    rex : (w : Bool) -> (r : Bits8) -> (x : Bits8) -> (b : Bits8) -> (force : Bool) -> OptionalByte
    rex w r x b force =
      let v = (if w then 8 else 0) .|. shiftL (hi r) 2 .|. shiftL (hi x) 1 .|. hi b
      in if v == 0 && not force then OptionalByte.none else OptionalByte.byte (0x40 .|. v)
      where
        hi : Bits8 -> Bits8            -- bit 3 of a register number
        hi n = shiftR n 3

    modrm : (md : Bits8) -> (reg : Bits8) -> (rm : Bits8) -> Bits8
    modrm md reg rm = shiftL md 6 .|. shiftL (lo reg) 3 .|. lo rm

    ||| The parts of an instruction of this legacy prefix (0 for none), REX
    ||| prefix, opcode (as Intel writes it), ModRM, SIB, displacement and
    ||| immediate. An opcode of 0x100 or more is read as its low byte, of
    ||| the two-byte map: its high byte must be 0x0F, and is not checked.
    parts : (legacy : Bits8) -> (rexPrefix : OptionalByte) -> (opcode : Bits16) ->
            (modrmByte, sibByte : OptionalByte) -> InstrFormat.DispWidth -> (disp : Int) ->
            InstrFormat.ImmWidth -> (imm : Int) -> InstrFormat
    parts p r o m s dw d iw i =
      InstrFormat.Parts (if p == 0 then OptionalByte.none else OptionalByte.byte p) r
        (if o >= 0x100 then InstrFormat.TwoByte else InstrFormat.OneByte) (cast o) m s dw d iw i

    ||| An instruction of no ModRM byte: REX · opcode · imm, of the REX
    ||| prefix given.
    opcodeForm : OptionalByte -> (opcode : Bits16) -> InstrFormat.ImmWidth -> (imm : Int) ->
                 InstrFormat
    opcodeForm r o iw i = parts 0 r o OptionalByte.none OptionalByte.none InstrFormat.NoDisp 0 iw i

    ||| An instruction of the form  legacy prefix · REX · opcode · ModRM · imm,
    ||| of a register operand in ModRM's rm, by its number.
    regForm : (legacy : Bits8) -> (w : Bool) -> (opcode : Bits16) -> (reg, rm : Bits8) ->
              (forceRex : Bool) -> InstrFormat.ImmWidth -> (imm : Int) -> InstrFormat
    regForm p w o reg rm forceRex iw i =
      parts p (rex w reg 0 rm forceRex) o (OptionalByte.byte (modrm 3 reg rm)) OptionalByte.none
        InstrFormat.NoDisp 0 iw i

    ||| Whether the number fits 8 bits, signed.
    fitsInt8 : Int -> Bool
    fitsInt8 x = x >= -128 && x <= 127

    ||| An instruction of 64-bit operands, a register in ModRM's rm, and an
    ||| immediate: of the opcode `o8` and the immediate in 8 bits if it fits
    ||| them, else of `o32` and the immediate in 32.
    immForm : (o8, o32 : Bits16) -> (reg, rm : Bits8) -> (imm : Int) -> InstrFormat
    immForm o8 o32 reg rm i =
      if fitsInt8 i then regForm 0 True o8 reg rm False InstrFormat.Imm8 i
      else regForm 0 True o32 reg rm False InstrFormat.Imm32 i

    ||| An immediate moved into a 64-bit register, by its number: in 32 bits,
    ||| sign-extended (C7 /0), if it fits them, else in 64 (B8+r), as the
    ||| `Int` of its 64 bits, read as signed or not.
    movImmForm : (reg : Bits8) -> Integer -> InstrFormat
    movImmForm r i =
      if fitsInt32 i then regForm 0 True 0xC7 0 r False InstrFormat.Imm32 (cast i)
      else opcodeForm (rex True 0 0 r False) (0xB8 + cast (lo r)) InstrFormat.Imm64 (cast i)

    ||| An instruction of the form
    ||| legacy prefix · REX · opcode · ModRM[·SIB·disp] · imm, of a memory
    ||| operand. For `MRip`, the displacement is `rel`, computed already.
    memForm : (legacy : Bits8) -> (w : Bool) -> (opcode : Bits16) -> (reg : Bits8) -> Asm.Mem ->
              (forceRex : Bool) -> InstrFormat.ImmWidth -> (imm : Int) -> InstrFormat
    memForm p w o reg mem forceRex iw i = case mem of
      Asm.MRip _ _ =>
        parts p (rex w reg 0 0 forceRex) o (OptionalByte.byte (modrm 0 reg 5)) OptionalByte.none
          InstrFormat.Disp32 rel iw i
      Asm.MBase base d =>
        let b = Asm.regNum base
            r = rex w reg 0 b forceRex
            -- rsp/r12 need a SIB
            sib = if lo b == 4 then OptionalByte.byte 0x24 else OptionalByte.none
        in if d == 0 && lo b /= 5      -- rbp/r13 cannot use mod 00
             then parts p r o (OptionalByte.byte (modrm 0 reg b)) sib InstrFormat.NoDisp 0 iw i
           else if fitsInt8 d
             then parts p r o (OptionalByte.byte (modrm 1 reg b)) sib InstrFormat.Disp8 d iw i
           else parts p r o (OptionalByte.byte (modrm 2 reg b)) sib InstrFormat.Disp32 d iw i

||| Encode with label-relative displacements already resolved to `rel`: the
||| instruction's bytes (`instrFormat`). For `Align`, `pc` is the address
||| of the instruction.
export
encodeRaw : (pc : Int) -> (rel : Int) -> Asm.Instr -> List Bits8
encodeRaw pc rel instr = InstrFormat.bytes (instrFormat pc rel instr)

------------------------------------------------------------------------------
-- What does not fit

||| Whether every field the encoder writes in fewer bits than its type holds
||| fits them: a displacement or an immediate in 32 bits, a 64-bit immediate
||| in 64. `encodeRaw` writes the low bits of a field that does not fit, so
||| `check` reports such an instruction instead. A displacement to a label
||| is checked there, once the label's address is known.
export
fieldsFit : Asm.Instr -> Bool
fieldsFit instr = case instr of
  Asm.MovRI _ i => fitsWord64 i
  Asm.MovRM _ m => memFits m
  Asm.MovMR m _ => memFits m
  Asm.MovMI m i => memFits m && fitsInt32 (cast i)
  Asm.Lea _ m => memFits m
  Asm.Load _ _ _ m => memFits m
  Asm.Store _ m _ => memFits m
  Asm.AluI _ _ i => fitsInt32 (cast i)
  Asm.AluRM _ _ m => memFits m
  Asm.AluMR _ m _ => memFits m
  Asm.TestI _ i => fitsInt32 (cast i)
  Asm.ImulI _ _ i => fitsInt32 (cast i)
  Asm.JmpM m => memFits m
  Asm.MovsdRM _ m => memFits m
  Asm.MovsdMR m _ => memFits m
  Asm.LockCmpxchg m _ => memFits m
  Asm.Quad v => fitsWord64 v
  _ => True
  where
    ||| A 64-bit immediate: a word, read as signed or unsigned.
    fitsWord64 : Integer -> Bool
    fitsWord64 x = x >= -9223372036854775808 && x <= 18446744073709551615

    memFits : Asm.Mem -> Bool
    memFits (Asm.MBase _ d) = fitsInt32 (cast d)
    memFits (Asm.MRip _ d) = fitsInt32 (cast d)

||| What the assembler could not encode faithfully (`check`), and what the
||| link could not write (`Native.Codegen.Link`).
public export
data AsmProblem
  = ||| A reference to a label that nothing defines. In code it encodes as
    ||| displacement 0.
    MissingLabel Asm.Label
  | ||| An instruction with a field that does not fit its bits, a displacement
    ||| to a label included. It encodes with the field's low bits.
    DoesNotFit Asm.Instr
  | ||| A label the text or its environment defines at or past the bound of
    ||| the labels' table (`LabelTable`), which has no place for it: a
    ||| reference to it is a missing label.
    LabelPastBound Asm.Label

export
Show AsmProblem where
  show (MissingLabel l) = "missing label " ++ show l
  show (DoesNotFit i) = "a field does not fit: " ++ show i
  show (LabelPastBound l) = "a label past the labels' bound: " ++ show l

||| Size in bytes at address `pc`, with no byte made (`InstrFormat.size`).
||| Independent of label values (rel32 everywhere).
export
instrSize : (pc : Int) -> Asm.Instr -> Int
instrSize pc i = cast (InstrFormat.size (instrFormat pc 0 i))

------------------------------------------------------------------------------
-- Two-pass assembly

||| Each instruction's size, in order, a byte each, by the instruction's
||| index in its sequence: what pass one found, read by the check and pass
||| two (`sizeAt`) with no list of the sizes made. A size of 255 bytes or
||| more, of an alignment or of raw bytes, is held as 255, and computed
||| again where it is read. Abstract: made by `measure` alone.
export
record Sizes where
  constructor MkSizes
  ||| The instructions it holds the sizes of, no more than the table's
  ||| bytes.
  count : Int
  table : Buffer

||| The size of the instruction at `index` of the sequence, at `pc`: the
||| size pass one found, or, past the instructions it measured or held as
||| 255, the size computed again (`instrSize`).
sizeAt : Sizes -> (index, pc : Int) -> Asm.Instr -> IO Int
sizeAt sizes index pc i =
  if index < sizes.count then held else pure (instrSize pc i)
  where
    held : IO Int
    held = do
      b <- getBits8 sizes.table index
      pure (if b == 255 then instrSize pc i else cast b)

||| Pass one, of a sequence placed at `base`: each instruction's size
||| (`Sizes`) and the sequence's, each instruction's size read from its
||| parts (`instrSize`), with no byte made, since no size depends on a
||| label; and the labels the sequence defines with no place in the table
||| it defines them in (`measure`).
public export
record Measured where
  constructor MkMeasured
  sizes : Sizes
  size : Int
  pastBound : List Asm.Label

||| Pass one (`Measured`), each label the sequence defines put in the table
||| at its address.
export
measure : LabelTable -> (base : Int) -> List Asm.Instr -> IO Measured
measure labels base is = do
  -- the table grows as the sequence is walked, which counting it first
  -- would walk once more: a walk of idris2-native's text costs about as
  -- much as measuring it does. A new buffer is all zeros, under every code
  -- generator, so a label's or a comment's size, 0, is not written; one
  -- that cannot be made holds no size, and each is computed again.
  table <- newBuffer 65536 >>= maybe emptyBuffer pure
  room <- rawSize table
  fromPrim (go table room 0 base [<] is)
  where
    -- the size of the instruction at `index` held in the table, of `room`
    -- bytes, if it has a place there
    hold : Buffer -> (room, index, size : Int) -> IO ()
    hold table room index n =
      if index < room then setBits8 table index (if n < 255 then cast n else 255) else pure ()

    -- the table grown to hold the instruction at `index`, to twice its
    -- bytes or more; as it is, if the larger one cannot be made
    grown : Buffer -> (room, index : Int) -> IO Buffer
    grown table room index = do
      Just t <- resizeBuffer table (max (2 * room) (index + 65536))
        | Nothing => pure table
      pure t

    -- the world passed by hand, so that the loop is a function of it, as
    -- pass two's is
    go : Buffer -> (room, index, pc : Int) -> SnocList Asm.Label -> List Asm.Instr ->
         PrimIO Measured
    go table room index pc past [] w =
      MkIORes (MkMeasured (MkSizes (min index room) table) (pc - base) (past <>> [])) w
    go table room index pc past (Asm.Lbl l :: rest) w =
      case toPrim (LabelTable.define labels l pc) w of
        MkIORes True w' => go table room (index + 1) pc past rest w'
        MkIORes False w' => go table room (index + 1) pc (past :< l) rest w'
    go table room index pc past (Asm.Comment _ :: rest) w = go table room (index + 1) pc past rest w
    go table room index pc past (i :: rest) w =
      let n = instrSize pc i
      in if index < room
           then case toPrim (hold table room index n) w of
             MkIORes () w' => go table room (index + 1) (pc + n) past rest w'
           else case toPrim (grown table room index) w of
             MkIORes t w1 => case toPrim (rawSize t) w1 of
               MkIORes room' w2 => case toPrim (hold t room' index n) w2 of
                 MkIORes () w3 => go t room' (index + 1) (pc + n) past rest w3

||| The environment of a sequence pass one measured, put in its labels'
||| table: the labels defined outside this text, at their final addresses,
||| such as the image's rodata and bss symbols (`planLayout` can run first
||| because sizes do not depend on labels). Text labels take precedence,
||| and of a label the environment gives twice, the first address: each is
||| put in the table unless it has an address there. What is wrong: the
||| labels with no place in the table.
export
defineEnvironment : LabelTable -> (env : List (Asm.Label, Int)) -> IO (List AsmProblem)
defineEnvironment labels env = go [<] env
  where
    go : SnocList AsmProblem -> List (Asm.Label, Int) -> IO (List AsmProblem)
    go past [] = pure (past <>> [])
    go past ((l, a) :: rest) = do
      placed <- LabelTable.defineNew labels l a
      go (if placed then past else past :< LabelPastBound l) rest

||| The label an instruction refers to, if any, and the constant added to it.
instrLabel : Asm.Instr -> Maybe (Asm.Label, Int)
instrLabel (Asm.Jmp l) = Just (l, 0)
instrLabel (Asm.Jcc _ l) = Just (l, 0)
instrLabel (Asm.Call l) = Just (l, 0)
instrLabel (Asm.MovRM _ (Asm.MRip l d)) = Just (l, d)
instrLabel (Asm.MovMR (Asm.MRip l d) _) = Just (l, d)
instrLabel (Asm.MovMI (Asm.MRip l d) _) = Just (l, d)
instrLabel (Asm.Lea _ (Asm.MRip l d)) = Just (l, d)
instrLabel (Asm.Load _ _ _ (Asm.MRip l d)) = Just (l, d)
instrLabel (Asm.Store _ (Asm.MRip l d) _) = Just (l, d)
instrLabel (Asm.AluRM _ _ (Asm.MRip l d)) = Just (l, d)
instrLabel (Asm.AluMR _ (Asm.MRip l d) _) = Just (l, d)
instrLabel (Asm.JmpM (Asm.MRip l d)) = Just (l, d)
instrLabel (Asm.MovsdRM _ (Asm.MRip l d)) = Just (l, d)
instrLabel (Asm.MovsdMR (Asm.MRip l d) _) = Just (l, d)
instrLabel (Asm.LockCmpxchg (Asm.MRip l d) _) = Just (l, d)
instrLabel _ = Nothing

||| An instruction of `size` bytes at `pc` that refers to a label at
||| `address`, plus a constant: the displacement to it from the end of the
||| instruction. The one rule for the displacement.
labelDisplacement : (pc, size, address, constant : Int) -> Int
labelDisplacement pc size a d = a + d - (pc + size)

||| An instruction of `size` bytes at `pc`: the displacement to the label it
||| refers to, from the end of the instruction (`labelDisplacement`); 0 for
||| none, and for a label with no address in the table. The world passed
||| by hand: an `IO` function whose body is a `case` of a pure value Idris
||| compiles as one that makes an action, at each instruction.
displacement : LabelTable -> (pc, size : Int) -> Asm.Instr -> PrimIO Int
displacement labels pc size i w = case instrLabel i of
  Nothing => MkIORes 0 w
  Just (l, d) => case toPrim (LabelTable.address labels l) w of
    MkIORes (Just a) w' => MkIORes (labelDisplacement pc size a d) w'
    MkIORes Nothing w' => MkIORes 0 w'

||| What is wrong with the sequence pass one measured, placed at `base`,
||| with its labels' table, its environment's labels in it
||| (`defineEnvironment`): the labels it defines with no place in the
||| table, the labels it cannot resolve and the fields that do not fit,
||| found with no instruction encoded.
export
check : LabelTable -> Measured -> (base : Int) -> List Asm.Instr -> IO (List AsmProblem)
check labels measured base is =
  fromPrim (go 0 base ([<] <>< map LabelPastBound measured.pastBound) is)
  where
    -- the instruction, unless its fields fit
    unfit : Asm.Instr -> (fits : Bool) -> List AsmProblem
    unfit i fits = if fits then [] else [DoesNotFit i]

    -- what is wrong with each instruction, of the size pass one found
    -- (`sizeAt`) at `pc`: a label with no address in the table or a field
    -- that does not fit, its displacement (`labelDisplacement`) included;
    -- the world passed by hand, as in pass two
    go : (index, pc : Int) -> SnocList AsmProblem -> List Asm.Instr -> PrimIO (List AsmProblem)
    go _ _ found [] w = MkIORes (found <>> []) w
    go index pc found (i :: rest) w = case toPrim (sizeAt measured.sizes index pc i) w of
      MkIORes size w1 => case instrLabel i of
        Nothing => go (index + 1) (pc + size) (found <>< unfit i (fieldsFit i)) rest w1
        Just (l, d) => case toPrim (LabelTable.address labels l) w1 of
          MkIORes (Just a) w2 =>
            go (index + 1) (pc + size)
              (found <>< unfit i (fieldsFit i && fitsInt32 (cast (labelDisplacement pc size a d))))
              rest w2
          MkIORes Nothing w2 =>
            go (index + 1) (pc + size) (found <>< (MissingLabel l :: unfit i (fieldsFit i)))
              rest w2

||| Pass two, of the sequence pass one measured, placed at `base`, with its
||| labels' table, its environment's labels in it (`defineEnvironment`):
||| each instruction's parts made once, with its displacement
||| (`displacement`), at the size pass one found, and written through a
||| span over the bytes it takes, part by part (`InstrFormat.write`), with
||| one check of the sink's end (`ByteSink.fits`). An instruction whose
||| parts are not of that size, or that does not fit before the sink's end,
||| stops the pass with no sink; one with a problem (`check`) is written
||| anyway.
export
assembleInto : ByteSink.Sink -> LabelTable -> Measured -> (base : Int) -> List Asm.Instr ->
               IO (Maybe ByteSink.Sink)
assembleInto sink labels measured base is = fromPrim (go (ByteSink.start sink) 0 base is)
  where
    -- The world passed by hand, so that the loop is a function of it: an
    -- `IO` loop with a clause that ends in a call, as a label's does here,
    -- Idris compiles as a function that makes an action at each
    -- instruction. The loop's place in the sink is a span of no bytes,
    -- which each instruction's writing ends at. A label or a comment takes
    -- no byte, and is skipped.
    go : ByteSink.Span sink 0 -> (index, pc : Int) -> List Asm.Instr ->
         PrimIO (Maybe ByteSink.Sink)
    sized : ByteSink.Span sink 0 -> (index, pc, size : Int) -> InstrFormat -> List Asm.Instr ->
            PrimIO (Maybe ByteSink.Sink)
    checked : ByteSink.Span sink 0 -> (index, pc, size : Int) -> (k : Nat) -> (f : InstrFormat) ->
              (0 _ : InstrFormat.size f = k) -> List Asm.Instr -> PrimIO (Maybe ByteSink.Sink)
    written : (at : ByteSink.Span sink 0) -> (index, pc, size : Int) -> (k : Nat) ->
              (f : InstrFormat) -> (0 _ : InstrFormat.size f = k) -> (fit : Bool) ->
              (0 _ : ByteSink.fits sink at k = fit) -> List Asm.Instr ->
              PrimIO (Maybe ByteSink.Sink)

    go at _ _ [] w = MkIORes (Just (ByteSink.past sink at)) w
    go at index pc (i :: rest) w = case i of
      Asm.Lbl _ => go at (index + 1) pc rest w
      Asm.Comment _ => go at (index + 1) pc rest w
      _ => case toPrim (sizeAt measured.sizes index pc i) w of
        MkIORes size w1 => case displacement labels pc size i w1 of
          MkIORes rel w2 => sized at index pc size (instrFormat pc rel i) rest w2

    -- The instruction's parts, if of the size pass one found: the size read
    -- once, as an argument, with its equation (`same`); whether they fit
    -- likewise (`fits`). A `with` would, but the world, a linear name,
    -- keeps one from being used here.
    sized at index pc size f rest w = checked at index pc size (InstrFormat.size f) f Refl rest w

    checked at index pc size k f same rest w =
      if cast k /= size then MkIORes Nothing w
      else written at index pc size k f same (ByteSink.fits sink at k) Refl rest w

    -- the parts written from the place, if they fit before the sink's end
    written at index pc size k f same False _ rest w = MkIORes Nothing w
    written at index pc size k f same True fits rest w =
      case toPrim (InstrFormat.write sink f (rewrite same in ByteSink.span sink at k fits)) w of
        MkIORes end w' => go end (index + 1) (pc + size) rest w'

||| Both passes with no environment, the labels' table of those the
||| sequence defines, the bytes made as a snoc-list, each instruction's
||| size computed where it is encoded, not read from pass one's
||| (`Sizes`), with what is wrong (`check`): the encoder's reference, for
||| its tests.
export
assemble : (base : Int) -> List Asm.Instr -> IO (SnocList Bits8, List AsmProblem)
assemble base is = do
  labels <- LabelTable.labelTable (foldl past 0 is)
  measured <- measure labels base is
  code <- go labels base [<] is
  problems <- check labels measured base is
  pure (code, problems)
  where
    -- one past the labels defined so far
    past : Nat -> Asm.Instr -> Nat
    past bound (Asm.Lbl l) = max bound (S l)
    past bound _ = bound

    go : LabelTable -> (pc : Int) -> SnocList Bits8 -> List Asm.Instr -> IO (SnocList Bits8)
    go _ _ acc [] = pure acc
    go labels pc acc (i :: rest) = do
      let size = instrSize pc i
      rel <- fromPrim (displacement labels pc size i)
      go labels (pc + size) (acc <>< encodeRaw pc rel i) rest
