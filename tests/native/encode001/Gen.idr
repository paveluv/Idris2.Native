||| Differential test of the x86-64 encoder against GNU as.
|||
||| Generates two instruction streams. Group A covers every constructor over
||| all registers, operand forms and immediate/displacement classes, in forms
||| where GNU as's encoding is canonical, so bytes must match exactly. Group B
||| holds forms where as legitimately chooses a different valid encoding
||| (accumulator-immediate short forms, D1 shift-by-one, rel8 branches); the
||| run script compares disassembly text for those instead.
|||
||| The encoder is the backend's assembler: it turns `Instr`, an Idris data
||| type of the x86-64 instructions the backend renders, into machine code.
||| GNU as is used here as a reference only; the product never runs it.
module Gen

import Compiler.Native.X86.Asm
import Compiler.Native.X86.Encode
import Data.Buffer
import Data.Builder
import Data.List
import Data.SortedMap
import System.File

regs : List Reg64
regs = [RAX, RCX, RDX, RBX, RSP, RBP, RSI, RDI, R8, R9, R10, R11, R12, R13, R14, R15]

nonAcc : List Reg64            -- everything but rax, whose imm32 forms as shortens
nonAcc = drop 1 regs

xmms : List Xmm
xmms = [XMM0, XMM1, XMM2, XMM3, XMM4, XMM5, XMM6, XMM7, XMM8, XMM9, XMM10, XMM11, XMM12, XMM13, XMM14, XMM15]

conds : List Cond
conds = [O, NO, B, AE, E, NE, BE, A, S, NS, P, NP, L, GE, LE, G]

alus : List AluOp
alus = [ADD, OR, AND, SUB, XOR, CMP]

shifts : List ShiftOp
shifts = [SHL, SHR, SAR]

sses : List SseOp
sses = [ADDSD, SUBSD, MULSD, DIVSD]

||| Displacements at every encoding boundary.
disps : List Int
disps = [0, 1, -1, 8, -8, 127, -128, 128, -129, 4096, -4096, 2147483647, -2147483648]

||| Immediates at every encoding boundary (imm8 / imm32 / imm64).
imms32 : List Int
imms32 = [0, 1, -1, 127, -128, 128, -129, 1000, -1000, 2147483647, -2147483648]

imms64 : List Integer
imms64 = [0, 1, -1, 2147483647, -2147483648, 2147483648, -2147483649,
          4294967296, 0x0000020000010001, 0x1DC0000000000001, 9223372036854775807, -9223372036854775808]

shiftCounts : List Bits8
shiftCounts = [2, 3, 7, 31, 32, 33, 63]      -- 1 is group B (as uses D1)

mems : List Mem
mems = [MBase b d | b <- regs, d <- disps]

-- Labels: 1 = data target, 2 = far code target (placed at the very end)
groupA : List Instr
groupA =
  -- rip-relative and branches first: the targets sit >127 bytes away, so as
  -- must use rel32 as we do
  [Jmp 2, Call 2] ++ [Jcc c 2 | c <- conds]
  ++ [Lea r (MRip 1 0) | r <- regs] ++ [MovRM r (MRip 1 0) | r <- regs] ++ [MovMR (MRip 1 0) r | r <- regs]
  ++ [JmpM (MRip 1 0), MovsdRM XMM4 (MRip 1 0), MovsdMR (MRip 1 0) XMM12, MovMI (MRip 1 0) 5, AluRM ADD RBX (MRip 1 0), AluMR CMP (MRip 1 0) R9,
      Load W8 False RCX (MRip 1 0), Store W16 (MRip 1 0) R10, LockCmpxchg (MRip 1 0) RDX]
  -- a displacement from the label, as a static's pointer tag needs
  ++ [Lea r (MRip 1 1) | r <- regs] ++ [MovRM RAX (MRip 1 (-8)), MovMR (MRip 1 15) R11, JmpM (MRip 1 (-1))]
  ++ [MovRR d s | d <- regs, s <- regs]
  ++ [MovRI r i | r <- regs, i <- imms64]
  ++ [MovRM r m | r <- regs, m <- mems]
  ++ [MovMR m r | m <- mems, r <- regs]
  ++ [MovMI m i | m <- mems, i <- imms32]
  ++ [Lea r m | r <- regs, m <- mems]
  ++ [Load w s r m | w <- [W8, W16, W32], s <- [False, True], r <- regs, m <- take 26 mems]
  ++ [Store w m r | w <- [W8, W16, W32], m <- take 26 mems, r <- regs]
  ++ [Alu op d s | op <- alus, d <- regs, s <- regs]
  ++ [AluI op r i | op <- alus, r <- nonAcc, i <- imms32]
  ++ [AluI op RAX i | op <- alus, i <- [0, 1, -1, 127, -128]]        -- rax with imm8 is canonical
  ++ [AluRM op r m | op <- alus, r <- regs, m <- take 26 mems]
  ++ [AluMR op m r | op <- alus, m <- take 26 mems, r <- regs]
  ++ [Test a b | a <- regs, b <- regs]
  ++ [TestI r i | r <- nonAcc, i <- imms32]
  ++ [Imul d s | d <- regs, s <- regs]
  ++ [ImulI d s i | d <- regs, s <- regs, i <- [1, -1, 127, -128, 128, 1000, 2147483647]]
  ++ [Cqo]
  ++ [Idiv r | r <- regs] ++ [DivU r | r <- regs] ++ [Neg r | r <- regs] ++ [Not r | r <- regs]
  ++ [ShiftI op r n | op <- shifts, r <- regs, n <- shiftCounts]
  ++ [ShiftCl op r | op <- shifts, r <- regs]
  ++ [JmpR r | r <- regs] ++ [CallR r | r <- regs] ++ [JmpM m | m <- mems]
  ++ [Ret]
  ++ [Push r | r <- regs] ++ [Pop r | r <- regs]
  ++ [Setcc c r | c <- conds, r <- regs]
  ++ [Cmov c d s | c <- conds, d <- regs, s <- take 4 regs] ++ [Cmov E d s | d <- take 4 regs, s <- regs]
  ++ [MovsdRM x m | x <- xmms, m <- take 26 mems] ++ [MovsdMR m x | m <- take 26 mems, x <- xmms]
  ++ [MovsdRR d s | d <- xmms, s <- xmms]
  ++ [Sse op d s | op <- sses, d <- xmms, s <- xmms]
  ++ [Ucomisd a b | a <- xmms, b <- xmms]
  ++ [Cvtsi2sd x r | x <- xmms, r <- regs] ++ [Cvttsd2si r x | r <- regs, x <- xmms]
  ++ [MovqXR x r | x <- xmms, r <- regs] ++ [MovqRX r x | r <- regs, x <- xmms]
  ++ [Syscall, Nop, Int3]
  ++ [LockCmpxchg m r | m <- take 26 mems, r <- regs]
  ++ [Align 16, Quad 0x1DC0000000000001, Lbl 1, Bytes [1, 2, 3, 4, 5], Align 8, Lbl 2]

groupB : List Instr
groupB =
  [AluI op RAX i | op <- alus, i <- [128, -129, 1000, 2147483647]]
  ++ [TestI RAX i | i <- imms32]
  ++ [ShiftI op r 1 | op <- shifts, r <- regs]
  ++ [Jmp 3, Jcc NE 3, Call 3, Lbl 3]

writeBytes : String -> List Bits8 -> IO ()
writeBytes path bs = do
  let n = length bs
  Just buf <- newBuffer (cast n) | Nothing => putStrLn "buffer allocation failed"
  traverse_ (\(i, b) => setBits8 buf (cast i) b) (zip [0 .. minus n 1] bs)
  Right () <- writeBufferToFile path buf (cast n) | Left err => putStrLn ("write failed: " ++ show err)
  pure ()

emit : String -> List Instr -> IO ()
emit name is = do
  let (code, _, missing) = assemble 0 is
      bytes = contents code
  writeBytes (name ++ ".bin") bytes
  ignore $ writeFile (name ++ ".s") (".intel_syntax noprefix\n.text\n" ++ concat (map (\i => show i ++ "\n") is))
  putStrLn (name ++ ": " ++ show (length is) ++ " instructions, " ++ show (length bytes) ++ " bytes, missing labels: " ++ show (length missing))

main : IO ()
main = do
  emit "groupA" groupA
  emit "groupB" groupB
