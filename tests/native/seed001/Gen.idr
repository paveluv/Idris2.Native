||| Three binaries on the runtime seed alone: a result delivered
||| through HALT, the abort stub, and the grow-only allocator exercised
||| through two slow paths and one fast-path sequence.
|||
||| The seed is the handful of machine routines every program links with
||| until the runtime is written in Idris: start-up, which maps the first
||| allocation window and calls `main` with the continuation HALT; HALT,
||| which exits with the value `main` returns; the abort stub, which every
||| construct the backend does not lower jumps to; and the allocator's slow
||| path. Each program here is a hand-written `main` in x86-64 instructions.
||| The routines that are the runtime library's now, `idris_start`, which the
||| entry calls, `idris_alloc_slow`, the allocation slow path, and
||| `idris_crash`, each program brings by hand.
module Gen

import Native.Codegen.ELF
import Native.Codegen.Link
import Native.Codegen.Linkage.Sym
import Native.Codegen.X86.Asm
import Native.Codegen.X86.Encode
import Native.HeapObj.Shape
import Native.HeapObj.ValEnc
import Native.Types.Enc
import Native.Types.Header
import Native.Types.Kind
import System.File

||| The word of fixnum n, under fixnum tag 1.
fix : Integer -> Integer
fix n = 2 * n + 1

SeedEnc : Enc
SeedEnc = { val := FixnumTag1 } defaultEnc

||| The header word of an object, which a program writes when it allocates.
hdr : {k : Kind} -> Header SeedEnc k -> Integer
hdr h = cast (encodeHeader h)

-- 1. main returns fixnum 42 through k = HALT. As an Idris program, a `main`
-- whose value is 42: it returns by jumping to its continuation, whose
-- address is the first word of the continuation object in r12.
exitProg : List Instr
exitProg = [Lbl (symLabel SymMain), MovRI RAX (fix 42), JmpM (MBase R12 0)]

-- 2. main hits the abort stub, as a program does at the first construct
-- the backend does not lower: `idris: unsupported`, status 70.
unsupportedProg : List Instr
unsupportedProg = [Lbl (symLabel SymMain), Jmp (symLabel SymUnsupported)]

-- 3. A (3 words) via the slow path; B (8 MiB, larger than a window) via the
-- slow path, filling its window exactly; C through the inline fast path (lea,
-- cmp with r14, ja to the slow path), which must therefore take the slow
-- path; C points at A, and A's field is read back through C: 42 means every
-- window is mapped, bumped and intact. A is an object of a constructor with
-- two fields, as `MkPair 42 0` would be, and C one of a constructor with one,
-- as `Just a` would be. The allocation window is the free memory from r15
-- to r14: the fast path bumps r15 when the object fits, and the slow path
-- maps a new window when it does not; this allocator never collects.
slow, done : Label
slow = reservedLabels
done = reservedLabels + 1

allocProg : List Instr
allocProg =
  [ Lbl (symLabel SymMain)
  , MovRI RDI 24, Call (symLabel SymAllocSlow)
  , MovRI RDX (hdr (ConH 1 2)), MovMR (MBase RAX 0) RDX        -- a CON of id 1 and 2 fields
  , MovRI RDX (fix 42), MovMR (MBase RAX 8) RDX
  , MovMI (MBase RAX 16) 0
  , MovRR RBX RAX                                              -- A
  , MovRI RDI 0x800000, Call (symLabel SymAllocSlow)
  , MovRI RDX 7, MovMR (MBase RAX 0x7FFFF8) RDX                -- B's last word
  , Lea RCX (MBase R15 16), Alu CMP RCX R14, Jcc A slow        -- fast path for C (16 bytes)
  , MovRR RAX R15, MovRR R15 RCX, Jmp done
  , Lbl slow, MovRI RDI 16, Call (symLabel SymAllocSlow)
  , Lbl done
  , MovRI RDX (hdr (ConH 2 1)), MovMR (MBase RAX 0) RDX        -- a CON of id 2 and 1 field
  , MovMR (MBase RAX 8) RBX                                    -- C.0 := A
  , MovRM RCX (MBase RAX 8), MovRM RAX (MBase RCX 8)           -- A.0 through C
  , JmpM (MBase R12 0) ]

||| `idris_crash(rdi = message, rsi = length)`: write(2, message, length),
||| then exit_group(1).
crashByHand : List Instr
crashByHand =
  [ Lbl (symLabel SymCrash)
  , MovRR RDX RSI, MovRR RSI RDI, MovRI RDI 2, MovRI RAX 1, Syscall
  , MovRI RDI 1, MovRI RAX 231, Syscall ]

||| `idris_start(rdi = entry, rsi = window)`, reduced to the first window:
||| mmap(NULL, window, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS,
||| -1, 0), whose address is the allocation pointer, and the window's end its
||| limit. The system call keeps rsi.
startByHand : List Instr
startByHand =
  [ Lbl (symLabel SymRuntimeStart)
  , MovRI RAX 9, MovRI RDI 0, MovRI RDX 3, MovRI R10 0x22, MovRI R8 (-1), MovRI R9 0, Syscall
  , MovRR R15 RAX, MovRR R14 RAX, Alu ADD R14 RSI
  , Ret ]

||| `idris_alloc_slow(rdi = n bytes)`, grow-only: a fresh window of a
||| megabyte and `n` more from the system, the object at its start, the rest
||| the allocation window; the object's address in rdi, where a routine's
||| result goes. r13 keeps `n` across the system call, which keeps it.
allocSlowByHand : List Instr
allocSlowByHand =
  [ Lbl (symLabel SymAllocSlow)
  , MovRR R13 RDI
  , Lea RSI (MBase RDI 1048576)
  , MovRI RAX 9, MovRI RDI 0, MovRI RDX 3, MovRI R10 0x22, MovRI R8 (-1), MovRI R9 0, Syscall
  , MovRR R15 RAX, Alu ADD R15 R13
  , MovRR R14 RAX, Alu ADD R14 RSI
  , MovRR RDI RAX
  , Ret ]

emit : String -> List Instr -> IO ()
emit name prog = case link SeedEnc (prog ++ startByHand ++ allocSlowByHand ++ crashByHand) of
  Left missing => putStrLn (name ++ ": unresolved labels " ++ show missing)
  Right image => do
    Right () <- writeImage name image
      | Left err => putStrLn (name ++ ": write failed: " ++ show err)
    putStrLn (name ++ ": " ++ show (imageSize image) ++ " bytes")

main : IO ()
main = do
  emit "exit42" exitProg
  emit "unsupported" unsupportedProg
  emit "alloc" allocProg
