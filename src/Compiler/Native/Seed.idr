||| The runtime seed: the handful of routines a binary needs before the
||| runtime exists as fragment Idris, written as instruction constants: data
||| in Idris, no assembler source, no C. Every routine names what supersedes
||| it, and the whole module goes once the runtime is written in the
||| fragment. x86-64 Linux only, with the register roles of
||| `Compiler.Native.X86.Target.x86_64`: r15 and r14 hold the allocation window,
||| r12 the current continuation.
module Compiler.Native.Seed

import public Compiler.Native.HeapObject
import Compiler.Native.X86.Target
import Compiler.Native.X86.Asm
import public Compiler.Native.X86.Encode   -- linkProgram reports AsmProblem
import Compiler.Native.ELF
import Compiler.Native.Bytes
import Data.List
import Data.Maybe
import Data.SortedMap

%default total

------------------------------------------------------------------------------
-- Symbols. The seed owns labels below `reservedLabels`; lowered code numbers
-- its own labels from there.

public export
data Sym
  = SymStart           -- `_start`: the ELF entry point
  | SymMain            -- the program's entry under the heap lowering; the caller of `link` defines it
  | SymHalt            -- `idris_halt`: the code of the HALT continuation; result in rax -> exit_group
  | SymCrash           -- `idris_crash(msg, len)`: write to fd 2, exit_group(1)
  | SymUnsupported     -- `idris_unsupported`: the abort stub for unlowered code; writes a message, exit_group(70)
  | SymAllocSlow       -- `idris_alloc_slow(n)`: the allocation slow path (grow-only here)
  | SymMmapFailed      -- internal: crash with the out-of-memory message
  | SymHALT            -- rodata: the static HALT continuation, the bottom of every continuation chain
  | SymMsgUnsupported  -- rodata
  | SymMsgNoMemory     -- rodata
  | SymArgs            -- bss: ARGS, sized by `Areas`: arguments beyond the argument registers
  | SymRoots           -- bss: ROOTS, sized by `Areas`: the root buffer of the rooting stubs
  | SymNRoots          -- bss: NROOTS, 1 word: the entries of ROOTS in use
  | SymScratch         -- bss: SCRATCH, sized by `Areas`: extra registers for register allocation
  | SymApply           -- `idris_apply(f, a)`: apply a closure to one argument (CPS)
  | SymExit            -- `idris_exit(status)`: exit_group with the status (direct)
  | SymAllocMutable    -- `idris_alloc_mutable(n)`: the only way a mutable object is allocated
  | SymStackLimit      -- bss: STACK_LIMIT, 1 word: the lowest the stack pointer may go in direct code
  | SymStackOverflow   -- `idris_stack_overflow`: where direct code's stack check fails; message, exit 1
  | SymMsgStackOverflow  -- rodata

public export
symLabel : Sym -> Label
symLabel SymStart = 0
symLabel SymMain = 1
symLabel SymHalt = 2
symLabel SymCrash = 3
symLabel SymUnsupported = 4
symLabel SymAllocSlow = 5
symLabel SymMmapFailed = 6
symLabel SymHALT = 7
symLabel SymMsgUnsupported = 8
symLabel SymMsgNoMemory = 9
symLabel SymArgs = 10
symLabel SymRoots = 11
symLabel SymNRoots = 12
symLabel SymScratch = 13
symLabel SymApply = 14
symLabel SymExit = 15
symLabel SymAllocMutable = 16
symLabel SymStackLimit = 17
symLabel SymStackOverflow = 18
symLabel SymMsgStackOverflow = 19

||| Names as the ABI documents write them (for dumps).
public export
symName : Sym -> String
symName SymStart = "_start"
symName SymMain = "main"
symName SymHalt = "idris_halt"
symName SymCrash = "idris_crash"
symName SymUnsupported = "idris_unsupported"
symName SymAllocSlow = "idris_alloc_slow"
symName SymMmapFailed = "idris_mmap_failed"
symName SymHALT = "HALT"
symName SymMsgUnsupported = "msg_unsupported"
symName SymMsgNoMemory = "msg_no_memory"
symName SymArgs = "ARGS"
symName SymRoots = "ROOTS"
symName SymNRoots = "NROOTS"
symName SymScratch = "SCRATCH"
symName SymApply = "idris_apply"
symName SymExit = "idris_exit"
symName SymAllocMutable = "idris_alloc_mutable"
symName SymStackLimit = "STACK_LIMIT"
symName SymStackOverflow = "idris_stack_overflow"
symName SymMsgStackOverflow = "msg_stack_overflow"

||| The first label a program may use for itself.
public export
reservedLabels : Label
reservedLabels = 64

------------------------------------------------------------------------------
-- Parameters

||| The default allocation window: 4 MiB. The seed never collects: when a
||| window is exhausted, it maps another of the same size, or larger if one
||| allocation needs more. A tiny window, chosen with `linkWith`, makes tests
||| take the slow path often.
export
windowBytes : Int
windowBytes = 4 * 1024 * 1024

||| Exit status of the abort stub (distinct from a crash's 1).
export
unsupportedStatus : Int
unsupportedStatus = 70

||| The most of the process stack direct code may use, whatever the stack's
||| limit: 1 GiB.
stackCap : Integer
stackCap = 1024 * 1024 * 1024

||| What the stack check leaves below the limit, for the arguments and
||| environment above the stack pointer at entry and for the frames of code
||| that does not check, such as a direct call's saved values: 256 KiB.
stackMargin : Int
stackMargin = 256 * 1024

||| The stack's limit assumed when `getrlimit` fails: Linux's default, 8 MiB.
defaultStackBytes : Integer
defaultStackBytes = 8 * 1024 * 1024

-- Linux x86-64 system calls and mmap arguments
sysWrite, sysMmap, sysGetrlimit, sysExitGroup : Integer
sysWrite = 1
sysMmap = 9
sysGetrlimit = 97
sysExitGroup = 231

rlimitStack : Integer
rlimitStack = 3

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

||| A 16-aligned code label preceded by its layout word, as every resume
||| point and `idris_halt` need: pad to 8 mod 16, the word, the label.
export
resumePoint : Label -> (layout : Integer) -> List Instr
resumePoint l w = [Align 16, Bytes (replicate 8 0xCC), Quad w, Lbl l]

------------------------------------------------------------------------------
-- The routines

||| `_start`: set the stack limit, map the first window, set `k` to HALT, and
||| enter the program. Superseded by the fragment runtime's start-up, which
||| also maps the fixed runtime stack; the seed runs direct code on the
||| process stack the kernel provides, 16-aligned.
|||
||| Direct code, which recursion in flat code deepens, checks the stack
||| pointer against `STACK_LIMIT` on entry: the stack pointer at start-up,
||| less the stack's limit (`getrlimit`, at most `stackCap`), plus
||| `stackMargin`. Below the limit, the kernel's guard gap still faults.
startText : ValEnc -> (window : Int) -> List Instr
startText venc window =
  [ Comment "_start: STACK_LIMIT, map the first window, k := HALT, enter main"
  , Lbl (symLabel SymStart)
  , MovRR RBX RSP                                 -- the stack pointer at entry
  , AluI SUB RSP 16, MovRR RSI RSP                -- a struct rlimit, which the syscall keeps rsi pointing to
  , MovRI RCX defaultStackBytes, MovMR (MBase RSI 0) RCX   -- left as it is if getrlimit fails
  , MovRI RDI rlimitStack, MovRI RAX sysGetrlimit, Syscall
  , MovRM RAX (MBase RSI 0)                       -- the soft limit
  , MovRI RCX stackCap, Alu CMP RAX RCX, Cmov A RAX RCX   -- at most the cap; unlimited is above it
  , MovRR RCX RBX, Alu SUB RCX RAX, AluI ADD RCX stackMargin
  , Lea RAX (MRip (symLabel SymStackLimit) 0), MovMR (MBase RAX 0) RCX
  , MovRR RSP RBX
  , MovRI RSI (cast window) ] ++ mmapCall ++
  [ MovRR R15 RAX                                 -- hp
  , Lea R14 (MBase RAX window)                    -- hplim
  , Lea R12 (MRip (symLabel SymHALT) (cast (pointerTag venc)))   -- k := HALT, a pointer word
  , AluI AND RSP (-16)                            -- generated code never moves rsp: 16-aligned at every direct call
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

||| `idris_crash(rdi = message, rsi = length)`: write to fd 2, exit 1.
||| Superseded by the fragment runtime's crash routine.
crashText : List Instr
crashText =
  [ Comment "idris_crash(msg, len)"
  , Lbl (symLabel SymCrash)
  , MovRR RDX RSI, MovRR RSI RDI, MovRI RDI 2, MovRI RAX sysWrite, Syscall
  , MovRI RDI 1, MovRI RAX sysExitGroup, Syscall ]

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

||| The seed's code, for allocation windows of the given size in bytes.
||| `idris_exit(rdi = status)`: exit_group with the status. Superseded by the
||| fragment runtime's exit, which flushes first.
exitText : List Instr
exitText =
  [ Comment "idris_exit(status)"
  , Lbl (symLabel SymExit)
  , MovRI RAX sysExitGroup, Syscall ]

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
seedText enc window = startText enc.val window ++ haltText ++ crashText ++ unsupportedText
                      ++ stackOverflowText
                      ++ allocSlowText window ++ allocMutableText ++ exitText
                      ++ applyText x86_64.abi enc.val

------------------------------------------------------------------------------
-- Data: rodata (HALT and the messages) and the bss areas

pad8 : List Bits8 -> List Bits8
pad8 bs = bs ++ zeros (cast (alignUp (cast (length bs)) 8 - cast (length bs)))

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

||| The sizes, in words, of the per-thread areas, which no fixed bound
||| limits: each is as large as the program's code and the seed's need, so
||| nothing writes past one. `ARGS` holds the arguments of a call beyond the
||| argument registers; `ROOTS` the entries of the largest rooting stub, of
||| which at most one is active at a time, since only the allocation slow
||| paths of generated code collect; `SCRATCH` the slots of the function with
||| the most, and the arguments of the largest closure `idris_apply` stages
||| there.
public export
record Areas where
  constructor MkAreas
  args : Nat
  roots : Nat
  scratch : Nat

||| The larger of each area.
export
maxAreas : Areas -> Areas -> Areas
maxAreas a b = MkAreas (max a.args b.args) (max a.roots b.roots) (max a.scratch b.scratch)

||| What the seed's own code needs: `idris_apply`'s slow path roots the
||| closure and its argument. What it stages for a closure is the program's
||| largest arity, which the program's areas cover.
export
seedAreas : Areas
seedAreas = MkAreas 0 2 0

||| The zero-initialised per-thread areas, 8-aligned, in bss: `ARGS`, then
||| `ROOTS`, `NROOTS`, `SCRATCH` and `STACK_LIMIT`.
export
seedBss : Areas -> List (Sym, Int)
seedBss a =
  let roots = 8 * cast a.args
      nroots = roots + 8 * cast a.roots
      limit = nroots + 8 + 8 * cast a.scratch
  in [ (SymArgs, 0), (SymRoots, roots), (SymNRoots, nroots), (SymScratch, nroots + 8), (SymStackLimit, limit) ]

export
seedBssSize : Areas -> Int
seedBssSize a = 8 * cast (a.args + a.roots + 1 + a.scratch + 1)

------------------------------------------------------------------------------
-- Linking: one image from the seed and a program

||| A static executable from the seed and the program's own instructions and
||| read-only data, with allocation windows of `window` bytes, a multiple of
||| 8, and the per-thread areas the program needs (`Areas`). The program
||| defines `symLabel SymMain`, which is entered with `k = HALT`, `hp`/`hplim`
||| set and the stack 16-aligned, and numbers its other labels from
||| `reservedLabels`. Each item of read-only data follows the seed's,
||| 8-aligned, at its label. Fails with what it could not assemble: labels it
||| could not resolve, and fields that do not fit.
export
linkProgram : (enc : Enc) -> {auto 0 _ : HasFixnums enc.val} ->
              (window : Int) -> (areas : Areas) -> (program : List Instr) ->
              (rodata : List (Label, List Bits8)) -> Either (List AsmProblem) (List Bits8)
linkProgram enc window areas program items =
  let text = seedText enc window ++ program
      tl = layout textBase text
      ts = codeSize textBase text
      (seedData, rsyms) = seedRodata tl
      (rodata, offsets) = foldl place (seedData, []) items
      as = maxAreas seedAreas areas
      lay = planLayout ts (cast (length rodata)) (seedBssSize as)
      env = fromList (map (\(s, off) => (symLabel s, rodataBase lay + off)) rsyms
                   ++ map (\(s, off) => (symLabel s, bssBase lay + off)) (seedBss as)
                   ++ map (\(l, off) => (l, rodataBase lay + off)) offsets)
      (bytes, labels, problems) = assembleWith env textBase text
      entry = fromMaybe textBase (lookup (symLabel SymStart) labels)
  in if null problems then Right (elfImage X86_64 lay bytes rodata (seedBssSize as) entry)
                      else Left problems
  where
    place : (List Bits8, List (Label, Int)) -> (Label, List Bits8) -> (List Bits8, List (Label, Int))
    place (bs, offs) (l, item) = (bs ++ pad8 item, offs ++ [(l, cast (length bs))])

||| `linkProgram` for a program that uses no per-thread area beyond the
||| seed's, with no read-only data of its own.
export
linkWith : (enc : Enc) -> {auto 0 _ : HasFixnums enc.val} ->
           (window : Int) -> (program : List Instr) -> Either (List AsmProblem) (List Bits8)
linkWith enc window program = linkProgram enc window seedAreas program []

||| `linkWith` the default window.
export
link : (enc : Enc) -> {auto 0 _ : HasFixnums enc.val} ->
       (program : List Instr) -> Either (List AsmProblem) (List Bits8)
link enc = linkWith enc windowBytes
