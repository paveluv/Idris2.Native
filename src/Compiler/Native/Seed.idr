||| The runtime seed: the handful of routines a binary needs before the
||| runtime exists as fragment Idris, written as instruction constants: data
||| in Idris, no assembler source, no C. Every routine names what supersedes
||| it, and the whole module goes once the runtime is written in the
||| fragment. x86-64 Linux only, with the register roles of
||| `Compiler.Native.X86.Target.x86_64`: r15 and r14 hold the allocation window,
||| r12 the current continuation.
module Compiler.Native.Seed

import public Compiler.Native.HeapObject
import public Compiler.Native.Linkage
import Compiler.Native.X86.Target
import Compiler.Native.X86.Asm
import Compiler.Native.Bytes
import Data.List
import Data.Maybe
import Data.SortedMap

%default total

-- Linux x86-64 system calls and mmap arguments
sysWrite, sysMmap, sysExitGroup : Integer
sysWrite = 1
sysMmap = 9
sysExitGroup = 231

protReadWrite, mapPrivateAnon : Integer
protReadWrite = 3      -- PROT_READ | PROT_WRITE
mapPrivateAnon = 0x22  -- MAP_PRIVATE | MAP_ANONYMOUS

||| mmap(NULL, rsi, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0) with
||| the length already in rsi; on return rax is the address or, if it is
||| unsigned-above -4096, an error.
mmapCall : List Instr
mmapCall =
  [ MovRI RAX sysMmap, MovRI RDI 0, MovRI RDX protReadWrite, MovRI R10 mapPrivateAnon
  , MovRI R8 (-1), MovRI R9 0, Syscall
  , AluI CMP RAX (-4096), Jcc A (symLabel SymMmapFailed) ]

------------------------------------------------------------------------------
-- The routines

||| `_start`, the ELF entry: the runtime's `idris_start` with the stack
||| pointer at entry, where the system put the arguments, and the allocation
||| window's size, which sets up the program; then `main`, entered under the
||| continuation HALT, as the heap lowering of continuations enters code. The
||| stack pointer at entry is 16-aligned, and is again when `idris_start`
||| returns, so every direct call generated code makes finds it aligned.
startText : ValEnc -> (window : Int) -> List Instr
startText venc window =
  [ Comment "_start: idris_start(entry, window), then main under k = HALT"
  , Lbl (symLabel SymStart)
  , MovRR RDI RSP, MovRI RSI (cast window)
  , Call (symLabel SymRuntimeStart)
  , Lea R12 (MRip (symLabel SymHALT) (cast (pointerTag venc)))   -- k := HALT, a pointer word
  , Jmp (symLabel SymMain) ]

||| `idris_halt`: HALT's code. Entered by `jmp [k]` with the final result in
||| rax; a fixnum's value becomes the exit status. Superseded by the fragment
||| runtime's halt, which prints non-fixnum results and flushes.
haltText : List Instr
haltText =
  [ Comment "idris_halt: result in rax (fixnum) -> exit_group" ] ++
  resumePoint (symLabel SymHalt) (layoutWord 0 0) ++
  [ MovRR RDI RAX, ShiftI SAR RDI 1
  , MovRI RAX sysExitGroup, Syscall ]

msgUnsupported, msgNoMemory, msgStackOverflow : List Bits8
msgUnsupported = map (cast . ord) (unpack "idris: unsupported\n")
msgNoMemory = map (cast . ord) (unpack "idris: cannot map memory\n")
msgStackOverflow = map (cast . ord) (unpack "idris: stack overflow\n")

||| `idris_stack_overflow`: where direct code goes when the stack pointer is
||| below `STACK_LIMIT`. Superseded by the fragment runtime's, which runs
||| direct code on a stack of its own.
stackOverflowText : List Instr
stackOverflowText =
  [ Comment "idris_stack_overflow: message, exit 1"
  , Lbl (symLabel SymStackOverflow)
  , Lea RSI (MRip (symLabel SymMsgStackOverflow) 0), MovRI RDX (cast (length msgStackOverflow))
  , MovRI RDI 2, MovRI RAX sysWrite, Syscall
  , MovRI RDI 1, MovRI RAX sysExitGroup, Syscall ]

||| `idris_unsupported`: the abort stub that every construct the backend does
||| not lower yet jumps to (`Compiler.Native.Native`). Disappears when the
||| lowering is complete.
unsupportedText : List Instr
unsupportedText =
  [ Comment "idris_unsupported: message, exit 70"
  , Lbl (symLabel SymUnsupported)
  , Lea RSI (MRip (symLabel SymMsgUnsupported) 0), MovRI RDX (cast (length msgUnsupported))
  , MovRI RDI 2, MovRI RAX sysWrite, Syscall
  , MovRI RDI (cast unsupportedStatus), MovRI RAX sysExitGroup, Syscall ]

||| `idris_alloc_slow(rdi = n bytes)`: returns the object in rax and publishes
||| a new window in hp/hplim (pinned, so the caller sees it). Grow-only: a
||| fresh window of max(windowBytes, n) bytes, never a collection; ROOTS is
||| untouched because nothing moves. Superseded by the fragment runtime's slow
||| path, which collects before it maps.
allocSlowText : (window : Int) -> List Instr
allocSlowText window =
  [ Comment "idris_alloc_slow(n): map a fresh window, bump"
  , Lbl (symLabel SymAllocSlow)
  , MovRR R13 RDI                                  -- n (r13 is scratch; syscall keeps it)
  , MovRI RSI (cast window)
  , Alu CMP RDI RSI, Cmov A RSI RDI ] ++ mmapCall ++  -- rsi := max(window, n)
  [ MovRR R15 RAX, MovRR R14 RAX, Alu ADD R14 RSI   -- the new window
  , MovRR RAX R15, Alu ADD R15 R13                  -- the object; hp += n
  , Ret
  , Lbl (symLabel SymMmapFailed)
  , Lea RDI (MRip (symLabel SymMsgNoMemory) 0), MovRI RSI (cast (length msgNoMemory))
  , Jmp (symLabel SymCrash) ]

||| `idris_alloc_mutable(rdi = n bytes)`: returns the space of a mutable object
||| in rax, as the inline allocation does: the window's bump, or the slow path
||| when the window is exhausted. A mutable object is allocated only by this
||| routine, never inline, so that a collector with a nursery can keep every
||| mutable object out of it by changing this routine alone. The seed has no
||| nursery, and bumps the shared window.
allocMutableText : List Instr
allocMutableText =
  [ Comment "idris_alloc_mutable(n): bump, or the slow path"
  , Lbl (symLabel SymAllocMutable)
  , MovRR RAX R15, MovRR RCX R15, Alu ADD RCX RDI
  , Alu CMP RCX R14, Jcc A (symLabel SymAllocSlow)  -- rdi still holds n
  , MovRR R15 RCX
  , Ret ]

||| `idris_apply(rdi = closure, rsi = argument)`, entered by a jump under the
||| current continuation in r12. If the argument completes the closure, the
||| filled arguments and the new one are laid out in `SCRATCH`, which is dead
||| across this transfer, then passed as the ABI passes `Val`s: in its word
||| registers and, beyond them, in `ARGS`; and the closure's code is entered
||| by a jump. r9 holds `SCRATCH`'s address meanwhile, so if r9 is a word
||| register it is loaded last, after rax takes the code address. If not,
||| a closure with one more argument is allocated and returned through r12;
||| across its slow path, the old closure and the argument are rooted in
||| `ROOTS`. Superseded by the fragment runtime's apply.
applyText : Abi -> ValEnc -> List Instr
applyText abi venc =
  [ Comment "idris_apply(closure, argument)"
  , Lbl (symLabel SymApply)
  , MovRR R10 RDI, MovRR R11 RSI                     -- closure, argument
  , MovRM RAX (MBase R10 (0 - pt))                   -- header
  , MovRR RCX RAX ] ++ part RCX ClosureArity ++      -- arity
  [ MovRR RDX RAX ] ++ part RDX ClosureFilled ++     -- arguments filled
  [ MovRR R8 RDX, AluI ADD R8 1                      -- arguments after this one
  , Alu CMP R8 RCX, Jcc B extend
  -- saturated: the filled arguments, then the new one, into SCRATCH
  , Lea R9 (MRip (symLabel SymScratch) 0)
  , Lea RSI (MBase R10 (16 - pt)), MovRR RDI R9, MovRR RAX RDX
  , Lbl copy, Test RAX RAX, Jcc E copied
  , MovRM RCX (MBase RSI 0), MovMR (MBase RDI 0) RCX
  , AluI ADD RSI 8, AluI ADD RDI 8, AluI SUB RAX 1, Jmp copy
  , Lbl copied, MovMR (MBase RDI 0) R11
  -- arguments beyond the word registers go to ARGS
  , AluI CMP R8 (cast nregs), Jcc BE regs
  , Lea RSI (MBase R9 (cast (8 * nregs))), Lea RDI (MRip (symLabel SymArgs) 0)
  , MovRR RAX R8, AluI SUB RAX (cast nregs)
  , Lbl copyArgs, Test RAX RAX, Jcc E regs
  , MovRM RCX (MBase RSI 0), MovMR (MBase RDI 0) RCX
  , AluI ADD RSI 8, AluI ADD RDI 8, AluI SUB RAX 1, Jmp copyArgs
  , Lbl regs ] ++ loads (\r => r /= R9) ++
  [ MovRM RAX (MBase R10 (8 - pt)) ] ++               -- the code address
  loads (== R9) ++
  [ JmpR RAX
  -- partial: a closure with one more argument, 16 + 8 * (filled + 1) bytes
  , Lbl extend
  , MovRR RCX R8, ShiftI SHL RCX 3, AluI ADD RCX 16
  , MovRR RSI R15, Alu ADD RSI RCX, Alu CMP RSI R14, Jcc A slow
  , MovRR RDI R15, MovRR R15 RSI
  , Lbl initClosure                                  -- rdi: the new closure
  , MovRM RAX (MBase R10 (0 - pt)), MovRR RDX RAX ] ++ part RDX ClosureFilled ++
  [ MovRI RSI (partUnit ClosureFilled), Alu ADD RAX RSI, MovMR (MBase RDI 0) RAX   -- one more filled
  , MovRM RAX (MBase R10 (8 - pt)), MovMR (MBase RDI 8) RAX           -- code
  , Lea RSI (MBase R10 (16 - pt)), Lea RCX (MBase RDI 16)
  , Lbl pcopy, Test RDX RDX, Jcc E pdone
  , MovRM RAX (MBase RSI 0), MovMR (MBase RCX 0) RAX
  , AluI ADD RSI 8, AluI ADD RCX 8, AluI SUB RDX 1, Jmp pcopy
  , Lbl pdone, MovMR (MBase RCX 0) R11
  , toPointer RAX RDI, JmpM (MBase R12 (0 - pt))     -- the new closure's pointer word
  -- the slow path: root the closure and the argument across it
  , Lbl slow
  , Lea RSI (MRip (symLabel SymNRoots) 0), MovRM RAX (MBase RSI 0)
  , MovRR RDX RAX, ShiftI SHL RDX 3, Lea RDI (MRip (symLabel SymRoots) 0), Alu ADD RDI RDX
  , MovMR (MBase RDI 0) R10, MovMR (MBase RDI 8) R11
  , AluI ADD RAX 2, MovMR (MBase RSI 0) RAX
  , MovRR RDI RCX, Call (symLabel SymAllocSlow)
  , Lea RSI (MRip (symLabel SymNRoots) 0), MovRM RDX (MBase RSI 0), AluI SUB RDX 2, MovMR (MBase RSI 0) RDX
  , ShiftI SHL RDX 3, Lea RCX (MRip (symLabel SymRoots) 0), Alu ADD RCX RDX
  , MovRM R10 (MBase RCX 0), MovRM R11 (MBase RCX 8)
  , MovRR RDI RAX, Jmp initClosure ]
  where
    ||| The pointer tag: the closure in r10 and the continuation in r12 are
    ||| pointer words, the closure allocated in rdi an address.
    pt : Int
    pt = cast (pointerTag venc)

    ||| The address in `s` as a pointer word in `d`.
    toPointer : (d, s : Reg64) -> Instr
    toPointer d s = if pt == 0 then MovRR d s else Lea d (MBase s pt)

    nregs : Nat
    nregs = length abi.wordRegs

    -- Load the word registers that satisfy `which` from the staged
    -- arguments in SCRATCH, at r9.
    loads : (Reg64 -> Bool) -> List Instr
    loads which = [ MovRM r (MBase R9 (cast (8 * i)))
                  | (i, r) <- zip [0 .. nregs] (map regOfNum abi.wordRegs), which r ]

    ||| A part of the closure header in `rax`, extracted into a register.
    part : Reg64 -> HeaderPart CLOSURE -> List Instr
    part r p = extractField r (fst (place p)) (snd (place p))

    -- local labels, below the program's
    extend, copy, copied, copyArgs, regs, initClosure, pcopy, pdone, slow : Label
    extend = 40
    copy = 41
    copied = 42
    copyArgs = 43
    regs = 44
    initClosure = 45
    pcopy = 46
    pdone = 47
    slow = 48

||| The seed's code, for allocation windows of the given size in bytes, under
||| the program's encodings, whose value encoding has fixnums: `idris_halt`
||| reads the program's result as a fixnum, which is the word shifted right by
||| one under either.
export
seedText : (enc : Enc) -> {auto 0 _ : HasFixnums enc.val} -> (window : Int) -> List Instr
seedText enc window = startText enc.val window ++ haltText ++ unsupportedText
                      ++ stackOverflowText
                      ++ allocSlowText window ++ allocMutableText
                      ++ applyText x86_64.abi enc.val

------------------------------------------------------------------------------
-- Data: rodata (HALT and the messages) and the bss areas

||| The seed's read-only data, given the text labels (HALT's code word is the
||| address of `idris_halt`), with each symbol's offset. HALT comes first, at
||| offset 0 of the 16-aligned section.
export
seedRodata : (textLabels : SortedMap Label Int) -> (List Bits8, List (Sym, Int))
seedRodata tl =
  let haltCode = fromMaybe 0 (lookup (symLabel SymHalt) tl)
      halt = le64 (cast haltCode) ++ le64 0            -- code, parent
      m1 = pad8 msgUnsupported
      m2 = pad8 msgNoMemory
      m3 = pad8 msgStackOverflow
  in ( halt ++ m1 ++ m2 ++ m3
     , [ (SymHALT, 0)
       , (SymMsgUnsupported, cast (length halt))
       , (SymMsgNoMemory, cast (length halt + length m1))
       , (SymMsgStackOverflow, cast (length halt + length m1 + length m2)) ] )

||| What the seed's own code needs: `idris_apply`'s slow path roots the
||| closure and its argument. What it stages for a closure is the program's
||| largest arity, which the program's areas cover.
export
seedAreas : Areas
seedAreas = MkAreas 0 2 0

||| The zero-initialised per-thread areas, 8-aligned, in bss: `ARGS`, then
||| `ROOTS`, `NROOTS`, `SCRATCH`, `STACK_LIMIT` and `ARGV`.
export
seedBss : Areas -> List (Sym, Int)
seedBss a =
  let roots = 8 * cast a.args
      nroots = roots + 8 * cast a.roots
      limit = nroots + 8 + 8 * cast a.scratch
  in [ (SymArgs, 0), (SymRoots, roots), (SymNRoots, nroots), (SymScratch, nroots + 8), (SymStackLimit, limit)
     , (SymArgv, limit + 8) ]

export
seedBssSize : Areas -> Int
seedBssSize a = 8 * cast (a.args + a.roots + 1 + a.scratch + 2)
