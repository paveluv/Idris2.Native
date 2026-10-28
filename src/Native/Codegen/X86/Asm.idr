||| x86-64 instruction ADT for the native backend.
|||
||| One constructor per encodable operand form, so the encoder
||| (Native.Codegen.X86.Encode) is total by case analysis: there is no way to
||| build an instruction the encoder cannot emit. Directives (labels,
||| alignment, literal words) are constructors too, so a code stream is one
||| `List Instr` and the assembler needs no second syntax.
|||
||| `Show` renders Intel syntax as GNU `as` accepts it (`.intel_syntax
||| noprefix`); this is used only by dumps and by the test-time oracle that
||| compares the encoder with GNU `as` (`tests/native/encode001`). Nothing in
||| the product path parses it back.
module Native.Codegen.X86.Asm

-- lint: exclude precision: imported whole by target-neutral modules until the targets are
-- separated, with AArch64 (Seed, Link, Linkage.Sym, Linkage.ResumePoint and
-- the driver use it; the separation moves the x86 code into this group and
-- puts a target's assembler behind an interface)

import Data.List

%default total

------------------------------------------------------------------------------
-- Registers

public export
data Reg64 = RAX | RCX | RDX | RBX | RSP | RBP | RSI | RDI
           | R8  | R9  | R10 | R11 | R12 | R13 | R14 | R15

||| Hardware register number 0..15; bit 3 goes into REX.
public export
regNum : Reg64 -> Bits8
regNum RAX = 0
regNum RCX = 1
regNum RDX = 2
regNum RBX = 3
regNum RSP = 4
regNum RBP = 5
regNum RSI = 6
regNum RDI = 7
regNum R8 = 8
regNum R9 = 9
regNum R10 = 10
regNum R11 = 11
regNum R12 = 12
regNum R13 = 13
regNum R14 = 14
regNum R15 = 15

public export
Eq Reg64 where
  a == b = regNum a == regNum b

public export
Show Reg64 where
  show RAX = "rax"
  show RCX = "rcx"
  show RDX = "rdx"
  show RBX = "rbx"
  show RSP = "rsp"
  show RBP = "rbp"
  show RSI = "rsi"
  show RDI = "rdi"
  show R8 = "r8"
  show R9 = "r9"
  show R10 = "r10"
  show R11 = "r11"
  show R12 = "r12"
  show R13 = "r13"
  show R14 = "r14"
  show R15 = "r15"

||| The register of an encoding number: the inverse of `regNum`, by which
||| `Native.Codegen.Target` numbers x86-64's registers. A number beyond 15
||| is r15's.
public export
regOfNum : Nat -> Reg64
regOfNum 0 = RAX
regOfNum 1 = RCX
regOfNum 2 = RDX
regOfNum 3 = RBX
regOfNum 4 = RSP
regOfNum 5 = RBP
regOfNum 6 = RSI
regOfNum 7 = RDI
regOfNum 8 = R8
regOfNum 9 = R9
regOfNum 10 = R10
regOfNum 11 = R11
regOfNum 12 = R12
regOfNum 13 = R13
regOfNum 14 = R14
regOfNum _ = R15

||| The low byte of a register, for `setcc` and byte stores.
export
showReg8 : Reg64 -> String
showReg8 RAX = "al"
showReg8 RCX = "cl"
showReg8 RDX = "dl"
showReg8 RBX = "bl"
showReg8 RSP = "spl"
showReg8 RBP = "bpl"
showReg8 RSI = "sil"
showReg8 RDI = "dil"
showReg8 r = show r ++ "b"

export
showReg16 : Reg64 -> String
showReg16 RAX = "ax"
showReg16 RCX = "cx"
showReg16 RDX = "dx"
showReg16 RBX = "bx"
showReg16 RSP = "sp"
showReg16 RBP = "bp"
showReg16 RSI = "si"
showReg16 RDI = "di"
showReg16 r = show r ++ "w"

export
showReg32 : Reg64 -> String
showReg32 RAX = "eax"
showReg32 RCX = "ecx"
showReg32 RDX = "edx"
showReg32 RBX = "ebx"
showReg32 RSP = "esp"
showReg32 RBP = "ebp"
showReg32 RSI = "esi"
showReg32 RDI = "edi"
showReg32 r = show r ++ "d"

public export
data Xmm = XMM0 | XMM1 | XMM2 | XMM3 | XMM4 | XMM5 | XMM6 | XMM7
         | XMM8 | XMM9 | XMM10 | XMM11 | XMM12 | XMM13 | XMM14 | XMM15

public export
xmmNum : Xmm -> Bits8
xmmNum XMM0 = 0
xmmNum XMM1 = 1
xmmNum XMM2 = 2
xmmNum XMM3 = 3
xmmNum XMM4 = 4
xmmNum XMM5 = 5
xmmNum XMM6 = 6
xmmNum XMM7 = 7
xmmNum XMM8 = 8
xmmNum XMM9 = 9
xmmNum XMM10 = 10
xmmNum XMM11 = 11
xmmNum XMM12 = 12
xmmNum XMM13 = 13
xmmNum XMM14 = 14
xmmNum XMM15 = 15

public export
Show Xmm where
  show x = "xmm" ++ show (cast {to = Nat} (xmmNum x))

||| The xmm register of a number: the inverse of `xmmNum`, by which
||| `Native.Codegen.Target` numbers floating-point registers. A number
||| beyond 15 is xmm15's.
public export
xmmOfNum : Nat -> Xmm
xmmOfNum 0 = XMM0
xmmOfNum 1 = XMM1
xmmOfNum 2 = XMM2
xmmOfNum 3 = XMM3
xmmOfNum 4 = XMM4
xmmOfNum 5 = XMM5
xmmOfNum 6 = XMM6
xmmOfNum 7 = XMM7
xmmOfNum 8 = XMM8
xmmOfNum 9 = XMM9
xmmOfNum 10 = XMM10
xmmOfNum 11 = XMM11
xmmOfNum 12 = XMM12
xmmOfNum 13 = XMM13
xmmOfNum 14 = XMM14
xmmOfNum _ = XMM15

------------------------------------------------------------------------------
-- Conditions and operation groups

||| Condition codes in hardware order (the low nibble of `jcc`/`setcc`/`cmovcc`).
||| The sign conditions are `Sign` and `NoSign`, not `S` and `NS`: `S` is the
||| Prelude's successor, which no name of ours shadows.
public export
data Cond = O | NO | B | AE | E | NE | BE | A | Sign | NoSign | P | NP | L | GE | LE | G

public export
Show Cond where
  show O = "o"
  show NO = "no"
  show B = "b"
  show AE = "ae"
  show E = "e"
  show NE = "ne"
  show BE = "be"
  show A = "a"
  show Sign = "s"
  show NoSign = "ns"
  show P = "p"
  show NP = "np"
  show L = "l"
  show GE = "ge"
  show LE = "le"
  show G = "g"

public export
condCode : Cond -> Bits8
condCode O = 0
condCode NO = 1
condCode B = 2
condCode AE = 3
condCode E = 4
condCode NE = 5
condCode BE = 6
condCode A = 7
condCode Sign = 8
condCode NoSign = 9
condCode P = 10
condCode NP = 11
condCode L = 12
condCode GE = 13
condCode LE = 14
condCode G = 15

||| The classic two-operand ALU group; `/digit` and opcodes share one table.
public export
data AluOp = ADD | OR | AND | SUB | XOR | CMP

public export
Show AluOp where
  show ADD = "add"
  show OR = "or"
  show AND = "and"
  show SUB = "sub"
  show XOR = "xor"
  show CMP = "cmp"

public export
aluDigit : AluOp -> Bits8
aluDigit ADD = 0
aluDigit OR = 1
aluDigit AND = 4
aluDigit SUB = 5
aluDigit XOR = 6
aluDigit CMP = 7

public export
data ShiftOp = SHL | SHR | SAR

public export
Show ShiftOp where
  show SHL = "shl"
  show SHR = "shr"
  show SAR = "sar"

public export
shiftDigit : ShiftOp -> Bits8
shiftDigit SHL = 4
shiftDigit SHR = 5
shiftDigit SAR = 7

||| The scalar double operations of SSE2: four of two doubles, and the
||| square root of one, written as the others with the destination and the
||| source.
public export
data SseOp = ADDSD | SUBSD | MULSD | DIVSD | SQRTSD

public export
Show SseOp where
  show ADDSD = "addsd"
  show SUBSD = "subsd"
  show MULSD = "mulsd"
  show DIVSD = "divsd"
  show SQRTSD = "sqrtsd"

public export
sseOpcode : SseOp -> Bits8
sseOpcode ADDSD = 0x58
sseOpcode SUBSD = 0x5C
sseOpcode MULSD = 0x59
sseOpcode DIVSD = 0x5E
sseOpcode SQRTSD = 0x51

||| Memory access width for the narrow loads and stores (64-bit is `Mov*`).
public export
data Width = W8 | W16 | W32

public export
Show Width where
  show W8 = "byte"
  show W16 = "word"
  show W32 = "dword"

------------------------------------------------------------------------------
-- Operands

public export
Label : Type
Label = Nat

||| Memory operands are a base register plus a constant displacement, the
||| IR's only memory operand, or RIP plus a label plus a constant, for code
||| and static addresses: the constant is a static's pointer tag, when the
||| encoding of uniform values has one. An instruction names a label only
||| relative to RIP, here or as a jump's or a call's target, so the code
||| holds no absolute address: a static's is formed by `lea` of its label.
public export
data Mem = MBase Reg64 Int
         | MRip Label Int

export
showLabel : Label -> String
showLabel l = "L" ++ show l

public export
Show Mem where
  show (MBase r d) = if d == 0 then "[" ++ show r ++ "]"
                     else if d < 0 then "[" ++ show r ++ "-" ++ show (negate d) ++ "]"
                     else "[" ++ show r ++ "+" ++ show d ++ "]"
  show (MRip l d) = "[rip+" ++ showLabel l
    ++ (if d == 0 then "" else if d < 0 then "-" ++ show (negate d) else "+" ++ show d) ++ "]"

------------------------------------------------------------------------------
-- Instructions

public export
data Instr : Type where
  -- 64-bit moves
  MovRR  : Reg64 -> Reg64 -> Instr
  ||| Materialise a constant: imm32 sign-extended when it fits, else imm64.
  ||| `mov r64, imm64` is the only x86-64 form that takes a full 64-bit
  ||| immediate, which a header word needs.
  MovRI  : Reg64 -> Integer -> Instr
  MovRM  : Reg64 -> Mem -> Instr
  MovMR  : Mem -> Reg64 -> Instr
  ||| Store a sign-extended 32-bit immediate.
  MovMI  : Mem -> Int -> Instr
  Lea    : Reg64 -> Mem -> Instr
  -- narrow memory access; loads zero-extend unless `signed`
  Load   : Width -> (signed : Bool) -> Reg64 -> Mem -> Instr
  Store  : Width -> Mem -> Reg64 -> Instr
  -- integer arithmetic
  Alu    : AluOp -> Reg64 -> Reg64 -> Instr
  AluI   : AluOp -> Reg64 -> Int -> Instr
  AluRM  : AluOp -> Reg64 -> Mem -> Instr
  AluMR  : AluOp -> Mem -> Reg64 -> Instr
  Test   : Reg64 -> Reg64 -> Instr
  TestI  : Reg64 -> Int -> Instr
  Imul   : Reg64 -> Reg64 -> Instr
  ImulI  : Reg64 -> Reg64 -> Int -> Instr
  Cqo    : Instr
  Idiv   : Reg64 -> Instr
  DivU   : Reg64 -> Instr
  ||| rdx:rax := rax * the register, unsigned.
  Mul    : Reg64 -> Instr
  Neg    : Reg64 -> Instr
  Not    : Reg64 -> Instr
  ShiftI : ShiftOp -> Reg64 -> Bits8 -> Instr
  ShiftCl : ShiftOp -> Reg64 -> Instr
  -- control
  Jmp    : Label -> Instr
  Jcc    : Cond -> Label -> Instr
  Call   : Label -> Instr
  ||| Jump to the address in a register: the IR's `Enter`.
  JmpR   : Reg64 -> Instr
  ||| Jump to the address stored in memory: under the heap lowering a return
  ||| is `jmp [r12]`, through the current continuation's first word.
  JmpM   : Mem -> Instr
  CallR  : Reg64 -> Instr
  Ret    : Instr
  Push   : Reg64 -> Instr
  Pop    : Reg64 -> Instr
  Setcc  : Cond -> Reg64 -> Instr
  Cmov   : Cond -> Reg64 -> Reg64 -> Instr
  -- scalar double
  MovsdRM : Xmm -> Mem -> Instr
  MovsdMR : Mem -> Xmm -> Instr
  MovsdRR : Xmm -> Xmm -> Instr
  Sse    : SseOp -> Xmm -> Xmm -> Instr
  Ucomisd : Xmm -> Xmm -> Instr
  Cvtsi2sd : Xmm -> Reg64 -> Instr
  Cvttsd2si : Reg64 -> Xmm -> Instr
  MovqXR : Xmm -> Reg64 -> Instr
  MovqRX : Reg64 -> Xmm -> Instr
  -- system
  Syscall : Instr
  LockCmpxchg : Mem -> Reg64 -> Instr
  Nop    : Instr
  Int3   : Instr
  -- directives
  Lbl    : Label -> Instr
  ||| Pad with `int3` to the given power-of-two boundary (never executed).
  Align  : Nat -> Instr
  ||| An 8-byte literal, e.g. a continuation layout word before a resume label.
  Quad   : Integer -> Instr
  Bytes  : List Bits8 -> Instr
  Comment : String -> Instr

public export
Show Instr where
  show y = case y of
    MovRR d s => "mov " ++ show d ++ ", " ++ show s
    MovRI d i => "mov " ++ show d ++ ", " ++ show i
    MovRM d m => "mov " ++ show d ++ ", " ++ sizedMem "qword" m
    MovMR m s => "mov " ++ sizedMem "qword" m ++ ", " ++ show s
    MovMI m i => "mov " ++ sizedMem "qword" m ++ ", " ++ show i
    Lea d m => "lea " ++ show d ++ ", " ++ show m
    Load W32 False d m => "mov " ++ showReg32 d ++ ", " ++ sizedMem "dword" m
    Load w s d m => loadMnemonic w s ++ " " ++ show d ++ ", " ++ sizedMem (show w) m
    Store w m s => "mov " ++ sizedMem (show w) m ++ ", " ++ showWidthReg w s
    Alu op d s => show op ++ " " ++ show d ++ ", " ++ show s
    AluI op d i => show op ++ " " ++ show d ++ ", " ++ show i
    AluRM op d m => show op ++ " " ++ show d ++ ", " ++ sizedMem "qword" m
    AluMR op m s => show op ++ " " ++ sizedMem "qword" m ++ ", " ++ show s
    Test a b => "test " ++ show a ++ ", " ++ show b
    TestI a i => "test " ++ show a ++ ", " ++ show i
    Imul d s => "imul " ++ show d ++ ", " ++ show s
    ImulI d s i => "imul " ++ show d ++ ", " ++ show s ++ ", " ++ show i
    Cqo => "cqo"
    Idiv r => "idiv " ++ show r
    DivU r => "div " ++ show r
    Mul r => "mul " ++ show r
    Neg r => "neg " ++ show r
    Not r => "not " ++ show r
    ShiftI op r n => show op ++ " " ++ show r ++ ", " ++ show (cast {to = Nat} n)
    ShiftCl op r => show op ++ " " ++ show r ++ ", cl"
    Jmp l => "jmp " ++ showLabel l
    Jcc c l => "j" ++ show c ++ " " ++ showLabel l
    Call l => "call " ++ showLabel l
    JmpR r => "jmp " ++ show r
    JmpM m => "jmp " ++ sizedMem "qword" m
    CallR r => "call " ++ show r
    Ret => "ret"
    Push r => "push " ++ show r
    Pop r => "pop " ++ show r
    Setcc c r => "set" ++ show c ++ " " ++ showReg8 r
    Cmov c d s => "cmov" ++ show c ++ " " ++ show d ++ ", " ++ show s
    MovsdRM x m => "movsd " ++ show x ++ ", " ++ sizedMem "qword" m
    MovsdMR m x => "movsd " ++ sizedMem "qword" m ++ ", " ++ show x
    MovsdRR d s => "movsd " ++ show d ++ ", " ++ show s
    Sse op d s => show op ++ " " ++ show d ++ ", " ++ show s
    Ucomisd a b => "ucomisd " ++ show a ++ ", " ++ show b
    Cvtsi2sd x r => "cvtsi2sd " ++ show x ++ ", " ++ show r
    Cvttsd2si r x => "cvttsd2si " ++ show r ++ ", " ++ show x
    MovqXR x r => "movq " ++ show x ++ ", " ++ show r
    MovqRX r x => "movq " ++ show r ++ ", " ++ show x
    Syscall => "syscall"
    LockCmpxchg m r => "lock cmpxchg " ++ sizedMem "qword" m ++ ", " ++ show r
    Nop => "nop"
    Int3 => "int3"
    Lbl l => showLabel l ++ ":"
    Align n => ".balign " ++ show n ++ ", 0xcc"
    Quad v => ".quad " ++ show v
    Bytes bs => ".byte " ++ concat (intersperse ", " (map (show . cast {to = Nat}) bs))
    Comment s => "# " ++ s
    where
      loadMnemonic : Width -> Bool -> String
      loadMnemonic W32 False = "mov"          -- mov r32, m32 zero-extends
      loadMnemonic W32 True = "movsxd"
      loadMnemonic _ True = "movsx"
      loadMnemonic _ False = "movzx"

      showWidthReg : Width -> Reg64 -> String
      showWidthReg W8 = showReg8
      showWidthReg W16 = showReg16
      showWidthReg W32 = showReg32

      sizedMem : String -> Mem -> String
      sizedMem sz m = sz ++ " ptr " ++ show m

||| Move the bit field `width` bits wide at bit `offset` of a register down to
||| bits 0 and up, clearing every bit above it: two shifts, or one when the
||| field reaches bit 63. The rendering of `LoadPart` and the seed's reading
||| of a closure header both extract a header part this way.
public export
extractField : Reg64 -> (offset, width : Nat) -> List Instr
extractField r off w =
  if off + w < 64
     then [ShiftI SHL r (cast (minus 64 (off + w))), ShiftI SHR r (cast (minus 64 w))]
     else [ShiftI SHR r (cast off)]
