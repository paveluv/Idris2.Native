||| x86-64 byte encoder and two-pass assembler.
|||
||| `encodeRaw` is a pure function from an instruction (with any label-relative
||| displacement already computed) to bytes, total over `Instr`. `assemble`
||| lays out a code stream: pass one assigns label addresses (every
||| instruction's size is independent of label values because branches and
||| RIP-relative operands always use rel32), pass two encodes with resolved
||| displacements. Alignment padding is `int3`, never executed.
module Compiler.Native.X86.Encode

import Compiler.Native.X86.Asm

import Compiler.Native.Bytes
import Data.Bits
import Data.List
import Data.SortedMap
%default total

------------------------------------------------------------------------------
-- Immediates (byte order helpers live in Compiler.Native.Bytes)

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
encodeRaw : (pc : Int) -> (rel : Int) -> Instr -> List Bits8
encodeRaw pc rel instr = case instr of
  MovRR d s => form [] True [0x89] (regNum s) (Left d) 0 False []
  MovRI d i =>
    if fitsInt32 i
      then form [] True [0xC7] 0 (Left d) 0 False (le32 (cast i))
      else rex True 0 0 (regNum d) False ++ [0xB8 + lo (regNum d)] ++ le64 i
  MovRM d m => form [] True [0x8B] (regNum d) (Right m) rel False []
  MovMR m s => form [] True [0x89] (regNum s) (Right m) rel False []
  MovMI m i => form [] True [0xC7] 0 (Right m) rel False (le32 i)
  Lea d m => form [] True [0x8D] (regNum d) (Right m) rel False []
  Load W8 False d m => form [] True [0x0F, 0xB6] (regNum d) (Right m) rel False []
  Load W8 True d m => form [] True [0x0F, 0xBE] (regNum d) (Right m) rel False []
  Load W16 False d m => form [] True [0x0F, 0xB7] (regNum d) (Right m) rel False []
  Load W16 True d m => form [] True [0x0F, 0xBF] (regNum d) (Right m) rel False []
  Load W32 False d m => form [] False [0x8B] (regNum d) (Right m) rel False []
  Load W32 True d m => form [] True [0x63] (regNum d) (Right m) rel False []
  Store W8 m s => form [] False [0x88] (regNum s) (Right m) rel (byteRegNeedsRex s) []
  Store W16 m s => form [0x66] False [0x89] (regNum s) (Right m) rel False []
  Store W32 m s => form [] False [0x89] (regNum s) (Right m) rel False []
  Alu op d s => form [] True [0x01 + 8 * aluDigit op] (regNum s) (Left d) 0 False []
  AluI op d i =>
    if fitsInt8 i then form [] True [0x83] (aluDigit op) (Left d) 0 False (le8 i)
    else form [] True [0x81] (aluDigit op) (Left d) 0 False (le32 i)
  AluRM op d m => form [] True [0x03 + 8 * aluDigit op] (regNum d) (Right m) rel False []
  AluMR op m s => form [] True [0x01 + 8 * aluDigit op] (regNum s) (Right m) rel False []
  Test a b => form [] True [0x85] (regNum b) (Left a) 0 False []
  TestI a i => form [] True [0xF7] 0 (Left a) 0 False (le32 i)
  Imul d s => form [] True [0x0F, 0xAF] (regNum d) (Left s) 0 False []
  ImulI d s i =>
    if fitsInt8 i then form [] True [0x6B] (regNum d) (Left s) 0 False (le8 i)
    else form [] True [0x69] (regNum d) (Left s) 0 False (le32 i)
  Cqo => [0x48, 0x99]
  Idiv r => form [] True [0xF7] 7 (Left r) 0 False []
  DivU r => form [] True [0xF7] 6 (Left r) 0 False []
  Neg r => form [] True [0xF7] 3 (Left r) 0 False []
  Not r => form [] True [0xF7] 2 (Left r) 0 False []
  ShiftI op r n => form [] True [0xC1] (shiftDigit op) (Left r) 0 False [n]
  ShiftCl op r => form [] True [0xD3] (shiftDigit op) (Left r) 0 False []
  Jmp _ => 0xE9 :: le32 rel
  Jcc c _ => [0x0F, 0x80 + condCode c] ++ le32 rel
  Call _ => 0xE8 :: le32 rel
  JmpR r => form [] False [0xFF] 4 (Left r) 0 False []
  JmpM m => form [] False [0xFF] 4 (Right m) rel False []
  CallR r => form [] False [0xFF] 2 (Left r) 0 False []
  Ret => [0xC3]
  Push r => rex False 0 0 (regNum r) False ++ [0x50 + lo (regNum r)]
  Pop r => rex False 0 0 (regNum r) False ++ [0x58 + lo (regNum r)]
  Setcc c r => form [] False [0x0F, 0x90 + condCode c] 0 (Left r) 0 (byteRegNeedsRex r) []
  Cmov c d s => form [] True [0x0F, 0x40 + condCode c] (regNum d) (Left s) 0 False []
  MovsdRM x m => form [0xF2] False [0x0F, 0x10] (xmmNum x) (Right m) rel False []
  MovsdMR m x => form [0xF2] False [0x0F, 0x11] (xmmNum x) (Right m) rel False []
  MovsdRR d s => form [0xF2] False [0x0F, 0x10] (xmmNum d) (Left (xmmAsReg s)) 0 False []
  Sse op d s => form [0xF2] False [0x0F, sseOpcode op] (xmmNum d) (Left (xmmAsReg s)) 0 False []
  Ucomisd a b => form [0x66] False [0x0F, 0x2E] (xmmNum a) (Left (xmmAsReg b)) 0 False []
  Cvtsi2sd x r => form [0xF2] True [0x0F, 0x2A] (xmmNum x) (Left r) 0 False []
  Cvttsd2si r x => form [0xF2] True [0x0F, 0x2C] (regNum r) (Left (xmmAsReg x)) 0 False []
  MovqXR x r => form [0x66] True [0x0F, 0x6E] (xmmNum x) (Left r) 0 False []
  MovqRX r x => form [0x66] True [0x0F, 0x7E] (xmmNum x) (Left r) 0 False []
  Syscall => [0x0F, 0x05]
  LockCmpxchg m r => form [0xF0] True [0x0F, 0xB1] (regNum r) (Right m) rel False []
  Nop => [0x90]
  Int3 => [0xCC]
  Lbl _ => []
  Align n => replicate (padding pc n) 0xCC
  Quad v => le64 v
  Bytes bs => bs
  Comment _ => []
  where
    -- the ModRM rm field only needs the register number; reuse Reg64's table
    xmmAsReg : Xmm -> Reg64
    xmmAsReg x = case xmmNum x of
      0 => RAX
      1 => RCX
      2 => RDX
      3 => RBX
      4 => RSP
      5 => RBP
      6 => RSI
      7 => RDI
      8 => R8
      9 => R9
      10 => R10
      11 => R11
      12 => R12
      13 => R13
      14 => R14
      _ => R15
    padding : Int -> Nat -> Nat
    padding at n = let m = cast {to = Int} n in
                   if m <= 1 then 0 else cast ((m - (at `mod` m)) `mod` m)

    ||| Byte-register operands 4..7 (spl, bpl, sil, dil) need a REX to be
    ||| addressed at all.
    byteRegNeedsRex : Reg64 -> Bool
    byteRegNeedsRex r = regNum r >= 4 && regNum r <= 7

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
        -> (reg : Bits8) -> Either Reg64 Mem -> (rip : Int) -> (forceRex : Bool)
        -> (imm : List Bits8) -> List Bits8
    form prefixes w opcode reg rm rip forceRex imm =
      let (b, x) = rmExt rm
      in prefixes ++ rex w reg x b forceRex ++ opcode ++ rmBytes reg rm rip ++ imm
      where
        ||| The B/X extension bits contributed by a register-or-memory operand.
        rmExt : Either Reg64 Mem -> (Bits8, Bits8)
        rmExt (Left r) = (regNum r, 0)
        rmExt (Right (MBase b _)) = (regNum b, 0)
        rmExt (Right (MRip _ _)) = (0, 0)

        ||| ModRM (+ SIB + displacement) for a register-or-memory operand.
        ||| For `MRip`, the caller supplies the already-computed rel32.
        rmBytes : (reg : Bits8) -> Either Reg64 Mem -> (rip : Int) -> List Bits8
        rmBytes reg x rip = case x of
          Left r => [modrm 3 reg (regNum r)]
          Right (MRip _ _) => modrm 0 reg 5 :: le32 rip
          Right (MBase base d) =>
            let b = regNum base
                sib : List Bits8
                sib = if lo b == 4 then [0x24] else []         -- rsp/r12 need a SIB
            in if d == 0 && lo b /= 5 then modrm 0 reg b :: sib     -- rbp/r13 cannot use mod 00
               else if fitsInt8 d then (modrm 1 reg b :: sib) ++ le8 d
               else (modrm 2 reg b :: sib) ++ le32 d
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
fieldsFit : Instr -> Bool
fieldsFit instr = case instr of
  MovRI _ i => fitsWord64 i
  MovRM _ m => memFits m
  MovMR m _ => memFits m
  MovMI m i => memFits m && fitsInt32 (cast i)
  Lea _ m => memFits m
  Load _ _ _ m => memFits m
  Store _ m _ => memFits m
  AluI _ _ i => fitsInt32 (cast i)
  AluRM _ _ m => memFits m
  AluMR _ m _ => memFits m
  TestI _ i => fitsInt32 (cast i)
  ImulI _ _ i => fitsInt32 (cast i)
  JmpM m => memFits m
  MovsdRM _ m => memFits m
  MovsdMR m _ => memFits m
  LockCmpxchg m _ => memFits m
  Quad v => fitsWord64 v
  _ => True
  where
    ||| A 64-bit immediate: a word, read as signed or unsigned.
    fitsWord64 : Integer -> Bool
    fitsWord64 x = x >= -9223372036854775808 && x <= 18446744073709551615

    memFits : Mem -> Bool
    memFits (MBase _ d) = fitsInt32 (cast d)
    memFits (MRip _ d) = fitsInt32 (cast d)

||| What `assembleWith` could not encode faithfully.
public export
data AsmProblem
  = ||| A reference to a label that nothing defines. It encodes as
    ||| displacement 0.
    MissingLabel Label
  | ||| An instruction with a field that does not fit its bits, a displacement
    ||| to a label included. It encodes with the field's low bits.
    DoesNotFit Instr

export
Show AsmProblem where
  show (MissingLabel l) = "missing label " ++ show l
  show (DoesNotFit i) = "a field does not fit: " ++ show i

||| Size in bytes at address `pc`. Independent of label values (rel32 everywhere).
export
instrSize : (pc : Int) -> Instr -> Int
instrSize pc i = cast (length (encodeRaw pc 0 i))

------------------------------------------------------------------------------
-- Two-pass assembly

||| Pass one: addresses of labels, given the address of the first instruction.
export
layout : (base : Int) -> List Instr -> SortedMap Label Int
layout base = go base empty
  where
    go : Int -> SortedMap Label Int -> List Instr -> SortedMap Label Int
    go _ m [] = m
    go pc m (Lbl l :: is) = go pc (insert l pc m) is
    go pc m (i :: is) = go (pc + instrSize pc i) m is

||| Total size of a sequence placed at `base` (label-independent, like `layout`).
export
codeSize : (base : Int) -> List Instr -> Int
codeSize base is = foldl (\pc, i => pc + instrSize pc i) base is - base

||| Pass two, with an environment of labels defined outside this text: the
||| image's rodata and bss symbols at their final addresses (`planLayout` can
||| run first because sizes do not depend on labels). Text labels take
||| precedence. A reference to an unknown label, and an instruction with a
||| field that does not fit, are encoded anyway and reported, so the caller
||| can fail loudly.
export
assembleWith : (env : SortedMap Label Int) -> (base : Int) -> List Instr
            -> (SnocList Bits8, SortedMap Label Int, List AsmProblem)
assembleWith env base is =
  let labels = foldl (\m, (l, a) => insert l a m) env (SortedMap.toList (layout base is))
  in go labels base [<] [<] is
  where
    ||| The label an instruction refers to, if any, and the constant added to it.
    labelOf : Instr -> Maybe (Label, Int)
    labelOf (Jmp l) = Just (l, 0)
    labelOf (Jcc _ l) = Just (l, 0)
    labelOf (Call l) = Just (l, 0)
    labelOf (MovRM _ (MRip l d)) = Just (l, d)
    labelOf (MovMR (MRip l d) _) = Just (l, d)
    labelOf (MovMI (MRip l d) _) = Just (l, d)
    labelOf (Lea _ (MRip l d)) = Just (l, d)
    labelOf (Load _ _ _ (MRip l d)) = Just (l, d)
    labelOf (Store _ (MRip l d) _) = Just (l, d)
    labelOf (AluRM _ _ (MRip l d)) = Just (l, d)
    labelOf (AluMR _ (MRip l d) _) = Just (l, d)
    labelOf (JmpM (MRip l d)) = Just (l, d)
    labelOf (MovsdRM _ (MRip l d)) = Just (l, d)
    labelOf (MovsdMR (MRip l d) _) = Just (l, d)
    labelOf (LockCmpxchg (MRip l d) _) = Just (l, d)
    labelOf _ = Nothing

    -- the bytes and the problems accumulate at their ends, instruction by
    -- instruction
    go : SortedMap Label Int -> Int -> SnocList Bits8 -> SnocList AsmProblem -> List Instr
      -> (SnocList Bits8, SortedMap Label Int, List AsmProblem)
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
assemble : (base : Int) -> List Instr -> (SnocList Bits8, SortedMap Label Int, List AsmProblem)
assemble = assembleWith empty
