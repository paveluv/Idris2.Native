||| x86-64 byte encoder and two-pass assembler.
|||
||| `encodeRaw` is a pure function from an instruction (with any label-relative
||| displacement already computed) to bytes, total over `Instr`. `assemble`
||| lays out a code stream: pass one assigns label addresses (every
||| instruction's size is independent of label values because branches and
||| RIP-relative operands always use rel32), pass two encodes with resolved
||| displacements. Alignment padding is `int3`, never executed.
module Native.Codegen.X86.Encode

import Native.Codegen.X86.Asm

import Data.Bits
import Data.List
import Data.SortedMap
import Native.Codegen.Bytes
%default total

------------------------------------------------------------------------------
-- Immediates (byte order helpers live in Native.Codegen.Bytes)

export
fitsInt8 : Int -> Bool
fitsInt8 x = x >= -128 && x <= 127

export
fitsInt32 : Integer -> Bool
fitsInt32 x = x >= -2147483648 && x <= 2147483647

------------------------------------------------------------------------------
-- The encoder

||| Encode with label-relative displacements already resolved to `rel`.
||| For `Align`, `pc` is the address of the instruction.
export
encodeRaw : (pc : Int) -> (rel : Int) -> Asm.Instr -> List Bits8
encodeRaw pc rel instr = case instr of
  Asm.MovRR d s => form [] True [0x89] (Asm.regNum s) (Left d) 0 False []
  Asm.MovRI d i =>
        if fitsInt32 i
          then form [] True [0xC7] 0 (Left d) 0 False (Bytes.le32 (cast i))
          else rex True 0 0 (Asm.regNum d) False ++ [0xB8 + lo (Asm.regNum d)] ++ Bytes.le64 i
  Asm.MovRM d m => form [] True [0x8B] (Asm.regNum d) (Right m) rel False []
  Asm.MovMR m s => form [] True [0x89] (Asm.regNum s) (Right m) rel False []
  Asm.MovMI m i => form [] True [0xC7] 0 (Right m) rel False (Bytes.le32 i)
  Asm.Lea d m => form [] True [0x8D] (Asm.regNum d) (Right m) rel False []
  Asm.Load Asm.W8 False d m => form [] True [0x0F, 0xB6] (Asm.regNum d) (Right m) rel False []
  Asm.Load Asm.W8 True d m => form [] True [0x0F, 0xBE] (Asm.regNum d) (Right m) rel False []
  Asm.Load Asm.W16 False d m => form [] True [0x0F, 0xB7] (Asm.regNum d) (Right m) rel False []
  Asm.Load Asm.W16 True d m => form [] True [0x0F, 0xBF] (Asm.regNum d) (Right m) rel False []
  Asm.Load Asm.W32 False d m => form [] False [0x8B] (Asm.regNum d) (Right m) rel False []
  Asm.Load Asm.W32 True d m => form [] True [0x63] (Asm.regNum d) (Right m) rel False []
  Asm.Store Asm.W8 m s => form [] False [0x88] (Asm.regNum s) (Right m) rel (byteRegNeedsRex s) []
  Asm.Store Asm.W16 m s => form [0x66] False [0x89] (Asm.regNum s) (Right m) rel False []
  Asm.Store Asm.W32 m s => form [] False [0x89] (Asm.regNum s) (Right m) rel False []
  Asm.Alu op d s => form [] True [0x01 + 8 * Asm.aluDigit op] (Asm.regNum s) (Left d) 0 False []
  Asm.AluI op d i =>
        if fitsInt8 i then form [] True [0x83] (Asm.aluDigit op) (Left d) 0 False (Bytes.le8 i)
        else form [] True [0x81] (Asm.aluDigit op) (Left d) 0 False (Bytes.le32 i)
  Asm.AluRM op d m =>
    form [] True [0x03 + 8 * Asm.aluDigit op] (Asm.regNum d) (Right m) rel False []
  Asm.AluMR op m s =>
    form [] True [0x01 + 8 * Asm.aluDigit op] (Asm.regNum s) (Right m) rel False []
  Asm.Test a b => form [] True [0x85] (Asm.regNum b) (Left a) 0 False []
  Asm.TestI a i => form [] True [0xF7] 0 (Left a) 0 False (Bytes.le32 i)
  Asm.Imul d s => form [] True [0x0F, 0xAF] (Asm.regNum d) (Left s) 0 False []
  Asm.ImulI d s i =>
        if fitsInt8 i then form [] True [0x6B] (Asm.regNum d) (Left s) 0 False (Bytes.le8 i)
        else form [] True [0x69] (Asm.regNum d) (Left s) 0 False (Bytes.le32 i)
  Asm.Cqo => [0x48, 0x99]
  Asm.Idiv r => form [] True [0xF7] 7 (Left r) 0 False []
  Asm.DivU r => form [] True [0xF7] 6 (Left r) 0 False []
  Asm.Mul r => form [] True [0xF7] 4 (Left r) 0 False []
  Asm.Neg r => form [] True [0xF7] 3 (Left r) 0 False []
  Asm.Not r => form [] True [0xF7] 2 (Left r) 0 False []
  Asm.ShiftI op r n => form [] True [0xC1] (Asm.shiftDigit op) (Left r) 0 False [n]
  Asm.ShiftCl op r => form [] True [0xD3] (Asm.shiftDigit op) (Left r) 0 False []
  Asm.Jmp _ => 0xE9 :: Bytes.le32 rel
  Asm.Jcc c _ => [0x0F, 0x80 + Asm.condCode c] ++ Bytes.le32 rel
  Asm.Call _ => 0xE8 :: Bytes.le32 rel
  Asm.JmpR r => form [] False [0xFF] 4 (Left r) 0 False []
  Asm.JmpM m => form [] False [0xFF] 4 (Right m) rel False []
  Asm.CallR r => form [] False [0xFF] 2 (Left r) 0 False []
  Asm.Ret => [0xC3]
  Asm.Push r => rex False 0 0 (Asm.regNum r) False ++ [0x50 + lo (Asm.regNum r)]
  Asm.Pop r => rex False 0 0 (Asm.regNum r) False ++ [0x58 + lo (Asm.regNum r)]
  Asm.Setcc c r => form [] False [0x0F, 0x90 + Asm.condCode c] 0 (Left r) 0 (byteRegNeedsRex r) []
  Asm.Cmov c d s => form [] True [0x0F, 0x40 + Asm.condCode c] (Asm.regNum d) (Left s) 0 False []
  Asm.MovsdRM x m => form [0xF2] False [0x0F, 0x10] (Asm.xmmNum x) (Right m) rel False []
  Asm.MovsdMR m x => form [0xF2] False [0x0F, 0x11] (Asm.xmmNum x) (Right m) rel False []
  Asm.MovsdRR d s => form [0xF2] False [0x0F, 0x10] (Asm.xmmNum d) (Left (xmmAsReg s)) 0 False []
  Asm.Sse op d s =>
    form [0xF2] False [0x0F, Asm.sseOpcode op] (Asm.xmmNum d) (Left (xmmAsReg s)) 0 False []
  Asm.Ucomisd a b => form [0x66] False [0x0F, 0x2E] (Asm.xmmNum a) (Left (xmmAsReg b)) 0 False []
  Asm.Cvtsi2sd x r => form [0xF2] True [0x0F, 0x2A] (Asm.xmmNum x) (Left r) 0 False []
  Asm.Cvttsd2si r x => form [0xF2] True [0x0F, 0x2C] (Asm.regNum r) (Left (xmmAsReg x)) 0 False []
  Asm.MovqXR x r => form [0x66] True [0x0F, 0x6E] (Asm.xmmNum x) (Left r) 0 False []
  Asm.MovqRX r x => form [0x66] True [0x0F, 0x7E] (Asm.xmmNum x) (Left r) 0 False []
  Asm.Syscall => [0x0F, 0x05]
  Asm.LockCmpxchg m r => form [0xF0] True [0x0F, 0xB1] (Asm.regNum r) (Right m) rel False []
  Asm.Nop => [0x90]
  Asm.Int3 => [0xCC]
  Asm.Lbl _ => []
  Asm.Align n => replicate (padding pc n) 0xCC
  Asm.Quad v => Bytes.le64 v
  Asm.Bytes bs => bs
  Asm.Comment _ => []
  where
    -- the ModRM rm field only needs the register number; reuse Reg64's table
    xmmAsReg : Asm.Xmm -> Asm.Reg64
    xmmAsReg x = case Asm.xmmNum x of
      0 => Asm.RAX
      1 => Asm.RCX
      2 => Asm.RDX
      3 => Asm.RBX
      4 => Asm.RSP
      5 => Asm.RBP
      6 => Asm.RSI
      7 => Asm.RDI
      8 => Asm.R8
      9 => Asm.R9
      10 => Asm.R10
      11 => Asm.R11
      12 => Asm.R12
      13 => Asm.R13
      14 => Asm.R14
      _ => Asm.R15
    padding : Int -> Nat -> Nat
    padding at n = let m = cast {to = Int} n in
                   if m <= 1 then 0 else cast ((m - (at `mod` m)) `mod` m)

    ||| Byte-register operands 4..7 (spl, bpl, sil, dil) need a REX to be
    ||| addressed at all.
    byteRegNeedsRex : Asm.Reg64 -> Bool
    byteRegNeedsRex r = Asm.regNum r >= 4 && Asm.regNum r <= 7

    lo : Bits8 -> Bits8            -- low three bits
    lo n = n .&. 7

    ||| REX prefix, or nothing when no bit is needed. `force` requests a bare
    ||| 0x40 (needed to address spl/bpl/sil/dil as byte registers).
    rex : (w : Bool) -> (r : Bits8) -> (x : Bits8) -> (b : Bits8) -> (force : Bool) -> List Bits8
    rex w r x b force =
      let v = (if w then 8 else 0) .|. shiftL (hi r) 2 .|. shiftL (hi x) 1 .|. hi b
      in if v == 0 && not force then [] else [0x40 .|. v]
      where
        hi : Bits8 -> Bits8            -- bit 3 of a register number
        hi n = shiftR n 3

    ||| One instruction of the form  prefixes · REX · opcode · ModRM[·SIB·disp] · imm.
    form : (prefixes : List Bits8) -> (w : Bool) -> (opcode : List Bits8)
        -> (reg : Bits8) -> Either Asm.Reg64 Asm.Mem -> (rip : Int) -> (forceRex : Bool)
        -> (imm : List Bits8) -> List Bits8
    form prefixes w opcode reg rm rip forceRex imm =
      let (b, x) = rmExt rm
      in prefixes ++ rex w reg x b forceRex ++ opcode ++ rmBytes reg rm rip ++ imm
      where
        ||| The B/X extension bits contributed by a register-or-memory operand.
        rmExt : Either Asm.Reg64 Asm.Mem -> (Bits8, Bits8)
        rmExt (Left r) = (Asm.regNum r, 0)
        rmExt (Right (Asm.MBase b _)) = (Asm.regNum b, 0)
        rmExt (Right (Asm.MRip _ _)) = (0, 0)

        ||| ModRM (+ SIB + displacement) for a register-or-memory operand.
        ||| For `MRip`, the caller supplies the already-computed rel32.
        rmBytes : (reg : Bits8) -> Either Asm.Reg64 Asm.Mem -> (rip : Int) -> List Bits8
        rmBytes reg x rip = case x of
          Left r => [modrm 3 reg (Asm.regNum r)]
          Right (Asm.MRip _ _) => modrm 0 reg 5 :: Bytes.le32 rip
          Right (Asm.MBase base d) =>
            let b = Asm.regNum base
                sib : List Bits8
                sib = if lo b == 4 then [0x24] else []         -- rsp/r12 need a SIB
            in if d == 0 && lo b /= 5 then modrm 0 reg b :: sib     -- rbp/r13 cannot use mod 00
               else if fitsInt8 d then (modrm 1 reg b :: sib) ++ Bytes.le8 d
               else (modrm 2 reg b :: sib) ++ Bytes.le32 d
          where
            modrm : (md : Bits8) -> (reg : Bits8) -> (rm : Bits8) -> Bits8
            modrm md reg rm = shiftL md 6 .|. shiftL (lo reg) 3 .|. lo rm

------------------------------------------------------------------------------
-- What does not fit

||| Whether every field the encoder writes in fewer bits than its type holds
||| fits them: a displacement or an immediate in 32 bits, a 64-bit immediate
||| in 64. `encodeRaw` writes the low bits of a field that does not fit, so
||| `assembleWith` reports such an instruction instead. A displacement to a
||| label is checked there, once the label's address is known.
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

||| What `assembleWith` could not encode faithfully.
export
data AsmProblem
  = ||| A reference to a label that nothing defines. It encodes as
    ||| displacement 0.
    MissingLabel Asm.Label
  | ||| An instruction with a field that does not fit its bits, a displacement
    ||| to a label included. It encodes with the field's low bits.
    DoesNotFit Asm.Instr

export
Show AsmProblem where
  show (MissingLabel l) = "missing label " ++ show l
  show (DoesNotFit i) = "a field does not fit: " ++ show i

||| Size in bytes at address `pc`. Independent of label values (rel32 everywhere).
export
instrSize : (pc : Int) -> Asm.Instr -> Int
instrSize pc i = cast (length (encodeRaw pc 0 i))

------------------------------------------------------------------------------
-- Two-pass assembly

||| Pass one: addresses of labels, given the address of the first instruction.
export
layout : (base : Int) -> List Asm.Instr -> SortedMap Asm.Label Int
layout base = go base empty
  where
    go : Int -> SortedMap Asm.Label Int -> List Asm.Instr -> SortedMap Asm.Label Int
    go _ m [] = m
    go pc m (Asm.Lbl l :: is) = go pc (insert l pc m) is
    go pc m (i :: is) = go (pc + instrSize pc i) m is

||| Total size of a sequence placed at `base` (label-independent, like `layout`).
export
codeSize : (base : Int) -> List Asm.Instr -> Int
codeSize base is = foldl (\pc, i => pc + instrSize pc i) base is - base

||| Pass two, with an environment of labels defined outside this text: the
||| image's rodata and bss symbols at their final addresses (`planLayout` can
||| run first because sizes do not depend on labels). Text labels take
||| precedence. A reference to an unknown label, and an instruction with a
||| field that does not fit, are encoded anyway and reported, so the caller
||| can fail loudly.
export
assembleWith : (env : SortedMap Asm.Label Int) -> (base : Int) -> List Asm.Instr
            -> (SnocList Bits8, SortedMap Asm.Label Int, List AsmProblem)
assembleWith env base is =
  let labels = foldl (\m, (l, a) => insert l a m) env (SortedMap.toList (layout base is))
  in go labels base [<] [<] is
  where
    ||| The label an instruction refers to, if any, and the constant added to it.
    labelOf : Asm.Instr -> Maybe (Asm.Label, Int)
    labelOf (Asm.Jmp l) = Just (l, 0)
    labelOf (Asm.Jcc _ l) = Just (l, 0)
    labelOf (Asm.Call l) = Just (l, 0)
    labelOf (Asm.MovRM _ (Asm.MRip l d)) = Just (l, d)
    labelOf (Asm.MovMR (Asm.MRip l d) _) = Just (l, d)
    labelOf (Asm.MovMI (Asm.MRip l d) _) = Just (l, d)
    labelOf (Asm.Lea _ (Asm.MRip l d)) = Just (l, d)
    labelOf (Asm.Load _ _ _ (Asm.MRip l d)) = Just (l, d)
    labelOf (Asm.Store _ (Asm.MRip l d) _) = Just (l, d)
    labelOf (Asm.AluRM _ _ (Asm.MRip l d)) = Just (l, d)
    labelOf (Asm.AluMR _ (Asm.MRip l d) _) = Just (l, d)
    labelOf (Asm.JmpM (Asm.MRip l d)) = Just (l, d)
    labelOf (Asm.MovsdRM _ (Asm.MRip l d)) = Just (l, d)
    labelOf (Asm.MovsdMR (Asm.MRip l d) _) = Just (l, d)
    labelOf (Asm.LockCmpxchg (Asm.MRip l d) _) = Just (l, d)
    labelOf _ = Nothing

    -- the bytes and the problems accumulate at their ends, instruction by
    -- instruction
    go : SortedMap Asm.Label Int -> Int -> SnocList Bits8 -> SnocList AsmProblem -> List Asm.Instr
      -> (SnocList Bits8, SortedMap Asm.Label Int, List AsmProblem)
    go labels _ acc problems [] = (acc, labels, problems <>> [])
    go labels pc acc problems (i :: rest) =
      let size = instrSize pc i
          (rel, missing) = case labelOf i of
            Nothing => (the Int 0, [])
            Just (l, d) => case lookup l labels of
              Just target => (target + d - (pc + size), [])
              Nothing => (0, [MissingLabel l])
          misfit = if fieldsFit i && fitsInt32 (cast rel) then [] else [DoesNotFit i]
      in go labels (pc + size) (acc <>< encodeRaw pc rel i) (problems <>< (missing ++ misfit)) rest

||| Pass two with no external labels.
export
assemble : (base : Int) -> List Asm.Instr ->
           (SnocList Bits8, SortedMap Asm.Label Int, List AsmProblem)
assemble = assembleWith empty
