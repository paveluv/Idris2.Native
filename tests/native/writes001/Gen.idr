-- The register allocator's description of what each x86-64 instruction
-- writes (`Native.Codegen.X86.Writes.writes`), checked against the
-- machine: every form is run, with its operands over the general
-- registers, and every register it changes must be one the table names.
--
-- `gen` makes `oracle`, a static image of the backend's own encoder, which
-- runs each sample between two dumps of the 16 general registers and the
-- low words of the 16 XMM registers. Before a sample every register is set
-- to a value of its own (the "poison"), and the registers the sample needs
-- to hold something sensible are set after: a memory operand's base, r13,
-- to a scratch area; a division's dividend and divisor; a system call's
-- number; a jump's target. The dump before is made after that setup, and
-- the setup is made again, the same, before the sample runs, since the
-- dump itself uses two registers. A dump stores the registers below the
-- stack pointer, so that it needs no register to address its stores, then
-- copies them to the sample's place. The image writes every dump to its
-- standard output and exits.
--
-- `gen check FILE` reads the dumps back and compares, for each sample, the
-- registers before and after: a register that changed and that `writes`
-- does not name is an undeclared write, which would let an allocator keep
-- a value in a register the instruction destroys. A declared write that
-- leaves its register as it was is no error: `cmov` may not move, and
-- `setcc` writes one byte.
module Main

import Data.Buffer
import Data.List
import Data.String
import Native.Codegen.ELF
import Native.Codegen.Platform
import Native.Codegen.X86.Asm
import Native.Codegen.X86.Encode
import Native.Codegen.X86.RegSet
import Native.Codegen.X86.Writes
import System
import System.File
import System.File.Buffer

%default total

gprsAll : List Reg64
gprsAll = [RAX, RCX, RDX, RBX, RSP, RBP, RSI, RDI, R8, R9, R10, R11, R12, R13, R14, R15]

xmmsAll : List Xmm
xmmsAll = [XMM0, XMM1, XMM2, XMM3, XMM4, XMM5, XMM6, XMM7,
           XMM8, XMM9, XMM10, XMM11, XMM12, XMM13, XMM14, XMM15]

||| The general registers an operand may be: all but the stack pointer,
||| which the dumps address from.
operands : List Reg64
operands = filter (/= RSP) gprsAll

||| A sample: the instruction, the setup it needs after the poison, and
||| the label it may jump to, which follows it.
record Sample where
  constructor MkSample
  setup : List Instr
  instr : Instr
  next : Maybe Label

-- Labels: the poison table, then one a sample.
initLabel : Label
initLabel = 0

memBase : Reg64
memBase = R13

||| r13 to the scratch area, for a memory operand.
atScratch : Int -> List Instr
atScratch scratch = [MovRI memBase (cast scratch)]

mem : Mem
mem = MBase memBase 8

||| A sample that jumps nowhere.
plain : List Instr -> Instr -> Label -> Sample
plain su i _ = MkSample su i Nothing

||| A sample that jumps or calls to the label after it, its setup and
||| instruction given the label.
jumping : (Label -> List Instr) -> (Label -> Instr) -> Label -> Sample
jumping su i l = MkSample (su l) (i l) (Just l)

||| Every form, with its register operands over all of them, but the
||| stack pointer and the registers a form needs for itself.
samples : (scratch : Int) -> List (Label -> Sample)
samples scratch =
  [ plain [] (MovRR d s) | d <- operands, s <- [RAX, RSP, R15] ] ++
  [ plain [] (MovRI d 12345678901) | d <- operands ] ++
  [ plain (atScratch scratch) (MovRM d mem) | d <- operands ] ++
  [ plain (atScratch scratch) (MovMR mem s) | s <- operands ] ++
  [ plain (atScratch scratch) (MovMI mem 77) ] ++
  [ plain (atScratch scratch) (Lea d mem) | d <- operands ] ++
  [ plain (atScratch scratch) (Load w sg d mem)
  | w <- [W8, W16, W32], sg <- [False, True], d <- operands ] ++
  [ plain (atScratch scratch) (Store w mem s) | w <- [W8, W16, W32], s <- operands ] ++
  [ plain [] (Alu op d s) | op <- [ADD, OR, AND, SUB, XOR, CMP], d <- operands, s <- [RCX, R9] ] ++
  [ plain [] (AluI op d 5) | op <- [ADD, OR, AND, SUB, XOR, CMP], d <- operands ] ++
  [ plain (atScratch scratch) (AluRM op d mem)
  | op <- [ADD, OR, AND, SUB, XOR, CMP], d <- operands ] ++
  [ plain (atScratch scratch) (AluMR op mem s)
  | op <- [ADD, OR, AND, SUB, XOR, CMP], s <- operands ] ++
  [ plain [] (Test d RSI) | d <- operands ] ++
  [ plain [] (TestI d 3) | d <- operands ] ++
  [ plain [] (Imul d R10) | d <- operands ] ++
  [ plain [] (ImulI d R11 9) | d <- operands ] ++
  [ plain [] Cqo ] ++
  [ plain [MovRI RAX 100, MovRI RDX 0, MovRI v 7] (Idiv v)
  | v <- filter (\r => r /= RAX && r /= RDX) operands ] ++
  [ plain [MovRI RAX 100, MovRI RDX 0, MovRI v 7] (DivU v)
  | v <- filter (\r => r /= RAX && r /= RDX) operands ] ++
  [ plain [] (Mul v) | v <- operands ] ++
  [ plain [] (Neg d) | d <- operands ] ++
  [ plain [] (Not d) | d <- operands ] ++
  [ plain [] (ShiftI op d 3) | op <- [SHL, SHR, SAR], d <- operands ] ++
  [ plain [] (ShiftCl op d) | op <- [SHL, SHR, SAR], d <- operands ] ++
  [ jumping (const []) Jmp ] ++
  [ jumping (const []) (Jcc c) | c <- [E, NE, L, GE, B, AE] ] ++
  [ jumping (const []) Call ] ++
  [ jumping (\l => [Lea r (MRip l 0)]) (const (JmpR r)) | r <- operands ] ++
  [ jumping (\l => [Lea r (MRip l 0)]) (const (CallR r)) | r <- operands ] ++
  [ jumping (\l => atScratch scratch ++ [Lea RAX (MRip l 0), MovMR mem RAX]) (const (JmpM mem)) ] ++
  [ jumping (\l => [Lea RAX (MRip l 0), Push RAX]) (const Ret) ] ++
  [ plain [] (Push s) | s <- operands ] ++
  [ plain [] (Pop d) | d <- operands ] ++
  [ plain [] (Setcc c d) | c <- [E, NE, B], d <- operands ] ++
  [ plain [] (Cmov c d R8) | c <- [E, NE], d <- operands ] ++
  [ plain (atScratch scratch) (MovsdRM x mem) | x <- xmmsAll ] ++
  [ plain (atScratch scratch) (MovsdMR mem x) | x <- xmmsAll ] ++
  [ plain [] (MovsdRR x XMM3) | x <- xmmsAll ] ++
  [ plain [] (Sse op x XMM5)
  | op <- [ADDSD, SUBSD, MULSD, DIVSD, SQRTSD], x <- xmmsAll ] ++
  [ plain [] (Ucomisd x XMM1) | x <- xmmsAll ] ++
  [ plain [] (Cvtsi2sd x RBX) | x <- xmmsAll ] ++
  [ plain [] (Cvttsd2si d XMM2) | d <- operands ] ++
  [ plain [] (MovqXR x RDI) | x <- xmmsAll ] ++
  [ plain [] (MovqRX d XMM4) | d <- operands ] ++
  [ plain [MovRI RAX 39] Syscall ] ++
  [ plain (atScratch scratch) (LockCmpxchg mem s) | s <- operands ] ++
  [ plain [] Nop ]

-- the words of a dump: the general registers, then the XMM registers'
-- low words
dumpWords : Int
dumpWords = 32

||| Every register set to its poison, from the table at `initLabel`.
poison : List Instr
poison =
  [ MovRM r (MRip initLabel (8 * cast (regNum r))) | r <- operands ] ++
  [ MovsdRM x (MRip initLabel (128 + 8 * cast (xmmNum x))) | x <- xmmsAll ]

||| The registers stored below the stack pointer, then copied to `at`.
dump : (at : Int) -> List Instr
dump at =
  [ MovMR (MBase RSP (-8 * (1 + cast (regNum r)))) r | r <- gprsAll ] ++
  [ MovsdMR (MBase RSP (-136 - 8 * cast (xmmNum x))) x | x <- xmmsAll ] ++
  [MovRI RAX (cast at)] ++
  concat [ [MovRM RCX (MBase RSP (-8 * (1 + k))), MovMR (MBase RAX (8 * k)) RCX]
         | k <- [0 .. dumpWords - 1] ]

||| The poison of each register: a word of its own for each general
||| register, a double of its own for each XMM register.
poisonTable : List Instr
poisonTable =
  [ Quad (0x0101010101010101 * (cast (regNum r) + 1) + 0x10) | r <- gprsAll ] ++
  [ Quad (0x3FF0000000000000 + 0x0000100000000000 * (cast (xmmNum x) + 1)) | x <- xmmsAll ]

||| The image's code, with the bss area at `area`: the stack pointer saved,
||| each sample between its dumps, the dumps written out, exit.
program : (area : Int) -> List Sample -> List Instr
program area ss =
  [Lbl 1, MovRI RAX (cast area), MovMR (MBase RAX 0) RSP]
  ++ concat (zipWith one [0 .. cast (length ss) - 1] ss)
  ++ [ MovRI RAX 1, MovRI RDI 1, MovRI RSI (cast (area + 8))
     , MovRI RDX (cast (8 * 2 * dumpWords * cast (length ss))), Syscall
     , MovRI RAX 231, MovRI RDI 0, Syscall
     , Lbl initLabel ] ++ poisonTable
  where
    one : Int -> Sample -> List Instr
    one k s =
      let before = area + 8 + 8 * 2 * dumpWords * k
          restore = [MovRI RAX (cast area), MovRM RSP (MBase RAX 0)]
      in restore ++ poison ++ s.setup ++ dump before
         ++ restore ++ poison ++ s.setup ++ [s.instr] ++ maybe [] (\l => [Lbl l]) s.next
         ++ dump (before + 8 * dumpWords)

||| The samples, their labels given out from 2.
labelled : Int -> List Sample
labelled scratch = zipWith (\l, f => f l) [2 .. 1 + length (samples scratch)] (samples scratch)

byteCount : SnocList Bits8 -> Int
byteCount = go 0
  where
    go : Int -> SnocList Bits8 -> Int
    go k [<] = k
    go k (sx :< _) = go (k + 1) sx

||| The image: assembled once with a stand-in for the area's address, of the
||| same size as an immediate, to lay the image out, then with the address.
covering
make : IO ()
make = do
  let n = cast (length (samples 0))
      bss = 8 + 8 * 2 * dumpWords * n + 4096
      stand = 0x500000
  (text0, _) <- assemble textBase (program stand (labelled (stand + bss - 4096)))
  let lay = planLayout (byteCount text0) 0 bss
      area = bssBase lay
  (text, missing) <- assemble textBase (program area (labelled (area + bss - 4096)))
  let True = byteCount text == byteCount text0
    | False => putStrLn "the text's size depends on the area's address"
  Right () <- writeImage "oracle"
                 (elfImage X86_64 lay (bytes (text <>> [])) (bytes []) bss textBase)
    | Left err => putStrLn ("write failed: " ++ show err)
  putStrLn ("\{show n} samples, missing labels: \{show (length missing)}")

||| Every sample's changed registers against what `writes` names.
covering
check : String -> IO ()
check file = do
  Right buf <- createBufferFromFile file
    | Left err => putStrLn ("cannot read \{file}: \{show err}")
  let ss = labelled 0
  bad <- traverse (report buf) (zip [0 .. cast (length ss) - 1] ss)
  let problems = concat bad
  if null problems
     then putStrLn ("\{show (length ss)} samples: every register that changed is declared")
     else traverse_ putStrLn problems
  where
    changedUndeclared : Buffer -> Int -> Sample -> IO (List String)
    changedUndeclared buf k s = do
      let w = writes s.instr
          before = 8 * 2 * dumpWords * k
      gs <- traverse (\r => do a <- getBits64 buf (before + 8 * cast (regNum r))
                               b <- getBits64 buf (before + 8 * dumpWords + 8 * cast (regNum r))
                               pure (if a /= b && not (hasGpr r w) then [show r] else []))
                     gprsAll
      xs <- traverse (\x => do let at = 128 + 8 * cast (xmmNum x)
                               a <- getBits64 buf (before + at)
                               b <- getBits64 buf (before + 8 * dumpWords + at)
                               pure (if a /= b && not (hasXmm x w) then [show x] else []))
                     xmmsAll
      pure (concat gs ++ concat xs)

    report : Buffer -> (Int, Sample) -> IO (List String)
    report buf (k, s) = do
      cs <- changedUndeclared buf k s
      pure (if null cs then [] else [show s.instr ++ ": " ++ unwords cs ++ " undeclared"])

covering
main : IO ()
main = do
  args <- getArgs
  case args of
    [_, "check", file] => check file
    _ => make
