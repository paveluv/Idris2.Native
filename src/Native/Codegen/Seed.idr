||| The runtime seed: what remains of the routines a binary needed before
||| the runtime existed as fragment Idris, written as instruction constants:
||| data in Idris, no assembler source, no C. The entry, HALT's code, the
||| abort stub, the stack overflow's exit and `idris_apply`; start-up,
||| allocation, collection, exit and crash are the runtime library's. Every
||| routine names what supersedes it, and the whole module goes once the
||| rest is written in the fragment. x86-64 Linux only, with the register
||| roles of `Native.Codegen.X86.Target.x86_64`: r15 and r14 hold the
||| allocation window, r12 the current continuation.
module Native.Codegen.Seed

import Native.Codegen.Bytes
import Native.Codegen.Linkage.Areas as Linkage
import Native.Codegen.Linkage.ResumePoint
import Native.Codegen.Linkage.Sym as Linkage
import Native.Codegen.Target
import Native.Codegen.X86.Asm
import Native.Codegen.X86.Target

import Data.List
import Data.Maybe
import Data.SortedMap
import Data.Zippable
import Native.Area
import Native.HeapObj.Enc as HeapObj
import Native.HeapObj.Header
import Native.HeapObj.Kind
import Native.HeapObj.LayoutWord
import Native.HeapObj.ValEnc as HeapObj

%default total

------------------------------------------------------------------------------
-- The routines

msgUnsupported, msgStackOverflow : List Bits8
msgUnsupported = map (cast . ord) (unpack "idris: unsupported\n")
msgStackOverflow = map (cast . ord) (unpack "idris: stack overflow\n")

||| The seed's code, for allocation windows of the given size in bytes, under
||| the program's encodings, whose value encoding has fixnums: `idris_halt`
||| reads the program's result as a fixnum, which is the word shifted right by
||| one under either.
export
seedText : (enc : HeapObj.Enc) -> {auto 0 _ : HeapObj.ValEnc.HasFixnums enc.val} -> (window : Int) -> List X86.Asm.Instr
seedText enc window = startText enc.val window ++ haltText enc.val ++ unsupportedText
                      ++ stackOverflowText
                      ++ applyText X86.Target.x86_64.abi enc.val
  where
    ||| `_start`, the ELF entry: the runtime's `idris_start` with the stack
    ||| pointer at entry, where the system put the arguments, and the allocation
    ||| window's size, which sets up the program; then `main`, entered under the
    ||| continuation HALT, as the heap lowering of continuations enters code. The
    ||| stack pointer at entry is 16-aligned, and is again when `idris_start`
    ||| returns, so every direct call generated code makes finds it aligned.
    startText : HeapObj.ValEnc -> (window : Int) -> List X86.Asm.Instr
    startText venc window =
      [ X86.Asm.Comment "_start: idris_start(entry, window), then main under k = HALT"
      , X86.Asm.Lbl (Linkage.Sym.symLabel Linkage.Sym.SymStart)
      , X86.Asm.MovRR X86.Asm.RDI X86.Asm.RSP, X86.Asm.MovRI X86.Asm.RSI (cast window)
      , X86.Asm.Call (Linkage.Sym.symLabel Linkage.Sym.SymRuntimeStart)
      , X86.Asm.Lea X86.Asm.R12
        (X86.Asm.MRip (Linkage.Sym.symLabel Linkage.Sym.SymHALT)
         (cast (HeapObj.ValEnc.pointerTag venc)))   -- k := HALT, a pointer word
      , X86.Asm.Jmp (Linkage.Sym.symLabel Linkage.Sym.SymMain) ]

    -- Linux x86-64 system calls and mmap arguments
    sysWrite, sysExitGroup : Integer
    sysWrite = 1
    sysExitGroup = 231

    ||| `idris_halt`: HALT's code. Entered by `jmp [k]` with the final result in
    ||| rax: a fixnum's value becomes the exit status, as a program written to
    ||| report through it gives; any other result, an object, ends the program
    ||| with status 0, as it does under Chez when `main` returns. Superseded by
    ||| the fragment runtime's halt, which prints non-fixnum results.
    haltText : HeapObj.ValEnc -> List X86.Asm.Instr
    haltText venc =
      [ X86.Asm.Comment "idris_halt: result in rax, a fixnum's value or 0 -> exit_group" ] ++
      Linkage.ResumePoint.resumePoint (Linkage.Sym.symLabel Linkage.Sym.SymHalt) (HeapObj.LayoutWord.layoutWord 0 0) ++
      [ X86.Asm.MovRR X86.Asm.RDI X86.Asm.RAX, X86.Asm.AluI X86.Asm.AND X86.Asm.RDI 1
      , X86.Asm.AluI X86.Asm.CMP X86.Asm.RDI (cast (HeapObj.ValEnc.pointerTag venc))
      , X86.Asm.Jcc X86.Asm.E object
      , X86.Asm.MovRR X86.Asm.RDI X86.Asm.RAX, X86.Asm.ShiftI X86.Asm.SAR X86.Asm.RDI 1, X86.Asm.Jmp exit
      , X86.Asm.Lbl object, X86.Asm.MovRI X86.Asm.RDI 0
      , X86.Asm.Lbl exit, X86.Asm.MovRI X86.Asm.RAX sysExitGroup, X86.Asm.Syscall ]
      where
        -- local labels, below the program's
        object, exit : X86.Asm.Label
        object = 49
        exit = 50

    ||| `idris_stack_overflow`: where direct code goes when the stack pointer is
    ||| below `STACK_LIMIT`. Superseded by the fragment runtime's, which runs
    ||| direct code on a stack of its own.
    stackOverflowText : List X86.Asm.Instr
    stackOverflowText =
      [ X86.Asm.Comment "idris_stack_overflow: message, exit 1"
      , X86.Asm.Lbl (Linkage.Sym.symLabel Linkage.Sym.SymStackOverflow)
      , X86.Asm.Lea X86.Asm.RSI (X86.Asm.MRip (Linkage.Sym.symLabel Linkage.Sym.SymMsgStackOverflow) 0),
        X86.Asm.MovRI X86.Asm.RDX (cast (length msgStackOverflow))
      , X86.Asm.MovRI X86.Asm.RDI 2, X86.Asm.MovRI X86.Asm.RAX sysWrite, X86.Asm.Syscall
      , X86.Asm.MovRI X86.Asm.RDI 1, X86.Asm.MovRI X86.Asm.RAX sysExitGroup, X86.Asm.Syscall ]

    ||| `idris_unsupported`: the abort stub that every construct the backend does
    ||| not lower yet jumps to (`Native.Codegen.Native`). Disappears when the
    ||| lowering is complete.
    unsupportedText : List X86.Asm.Instr
    unsupportedText =
      [ X86.Asm.Comment "idris_unsupported: message, exit 70"
      , X86.Asm.Lbl (Linkage.Sym.symLabel Linkage.Sym.SymUnsupported)
      , X86.Asm.Lea X86.Asm.RSI (X86.Asm.MRip (Linkage.Sym.symLabel Linkage.Sym.SymMsgUnsupported) 0),
        X86.Asm.MovRI X86.Asm.RDX (cast (length msgUnsupported))
      , X86.Asm.MovRI X86.Asm.RDI 2, X86.Asm.MovRI X86.Asm.RAX sysWrite, X86.Asm.Syscall
      , X86.Asm.MovRI X86.Asm.RDI (cast unsupportedStatus), X86.Asm.MovRI X86.Asm.RAX sysExitGroup, X86.Asm.Syscall ]
      where
        -- the exit status of the abort stub, distinct from a crash's 1
        unsupportedStatus : Int
        unsupportedStatus = 70

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
    applyText : Target.Abi -> HeapObj.ValEnc -> List X86.Asm.Instr
    applyText abi venc =
      [ X86.Asm.Comment "idris_apply(closure, argument)"
      , X86.Asm.Lbl (Linkage.Sym.symLabel Linkage.Sym.SymApply)
      , X86.Asm.MovRR X86.Asm.R10 X86.Asm.RDI,
        X86.Asm.MovRR X86.Asm.R11 X86.Asm.RSI                     -- closure, argument
      , X86.Asm.MovRM X86.Asm.RAX (X86.Asm.MBase X86.Asm.R10 (0 - pt))                   -- header
      , X86.Asm.MovRR X86.Asm.RCX X86.Asm.RAX ] ++ part X86.Asm.RCX HeapObj.Header.ClosureArity ++      -- arity
      [ X86.Asm.MovRR X86.Asm.RDX X86.Asm.RAX ] ++ part X86.Asm.RDX HeapObj.Header.ClosureFilled
        ++     -- arguments filled
      [ X86.Asm.MovRR X86.Asm.R8 X86.Asm.RDX,
        X86.Asm.AluI X86.Asm.ADD X86.Asm.R8 1                      -- arguments after this one
      , X86.Asm.Alu X86.Asm.CMP X86.Asm.R8 X86.Asm.RCX, X86.Asm.Jcc X86.Asm.B extend
      -- saturated: the filled arguments, then the new one, into SCRATCH
      , X86.Asm.Lea X86.Asm.R9 (X86.Asm.MRip (Linkage.Sym.symLabel Linkage.Sym.SymScratch) 0)
      , X86.Asm.Lea X86.Asm.RSI (X86.Asm.MBase X86.Asm.R10 (16 - pt)), X86.Asm.MovRR X86.Asm.RDI X86.Asm.R9,
        X86.Asm.MovRR X86.Asm.RAX X86.Asm.RDX
      , X86.Asm.Lbl copy, X86.Asm.Test X86.Asm.RAX X86.Asm.RAX, X86.Asm.Jcc X86.Asm.E copied
      , X86.Asm.MovRM X86.Asm.RCX (X86.Asm.MBase X86.Asm.RSI 0), X86.Asm.MovMR (X86.Asm.MBase X86.Asm.RDI 0) X86.Asm.RCX
      , X86.Asm.AluI X86.Asm.ADD X86.Asm.RSI 8, X86.Asm.AluI X86.Asm.ADD X86.Asm.RDI 8,
        X86.Asm.AluI X86.Asm.SUB X86.Asm.RAX 1, X86.Asm.Jmp copy
      , X86.Asm.Lbl copied, X86.Asm.MovMR (X86.Asm.MBase X86.Asm.RDI 0) X86.Asm.R11
      -- arguments beyond the word registers go to ARGS
      , X86.Asm.AluI X86.Asm.CMP X86.Asm.R8 (cast nregs), X86.Asm.Jcc X86.Asm.BE regs
      , X86.Asm.Lea X86.Asm.RSI (X86.Asm.MBase X86.Asm.R9 (cast (8 * nregs))),
        X86.Asm.Lea X86.Asm.RDI (X86.Asm.MRip (Linkage.Sym.symLabel Linkage.Sym.SymArgs) 0)
      , X86.Asm.MovRR X86.Asm.RAX X86.Asm.R8, X86.Asm.AluI X86.Asm.SUB X86.Asm.RAX (cast nregs)
      , X86.Asm.Lbl copyArgs, X86.Asm.Test X86.Asm.RAX X86.Asm.RAX, X86.Asm.Jcc X86.Asm.E regs
      , X86.Asm.MovRM X86.Asm.RCX (X86.Asm.MBase X86.Asm.RSI 0), X86.Asm.MovMR (X86.Asm.MBase X86.Asm.RDI 0) X86.Asm.RCX
      , X86.Asm.AluI X86.Asm.ADD X86.Asm.RSI 8, X86.Asm.AluI X86.Asm.ADD X86.Asm.RDI 8,
        X86.Asm.AluI X86.Asm.SUB X86.Asm.RAX 1, X86.Asm.Jmp copyArgs
      , X86.Asm.Lbl regs ] ++ loads (\r => r /= X86.Asm.R9) ++
      [ X86.Asm.MovRM X86.Asm.RAX (X86.Asm.MBase X86.Asm.R10 (8 - pt)) ] ++               -- the code address
      loads (== X86.Asm.R9) ++
      [ X86.Asm.JmpR X86.Asm.RAX
      -- partial: a closure with one more argument, 16 + 8 * (filled + 1) bytes
      , X86.Asm.Lbl extend
      , X86.Asm.MovRR X86.Asm.RCX X86.Asm.R8, X86.Asm.ShiftI X86.Asm.SHL X86.Asm.RCX 3,
        X86.Asm.AluI X86.Asm.ADD X86.Asm.RCX 16
      , X86.Asm.MovRR X86.Asm.RSI X86.Asm.R15, X86.Asm.Alu X86.Asm.ADD X86.Asm.RSI X86.Asm.RCX,
        X86.Asm.Alu X86.Asm.CMP X86.Asm.RSI X86.Asm.R14, X86.Asm.Jcc X86.Asm.A slow
      , X86.Asm.MovRR X86.Asm.RDI X86.Asm.R15, X86.Asm.MovRR X86.Asm.R15 X86.Asm.RSI
      , X86.Asm.Lbl initClosure                                  -- rdi: the new closure
      , X86.Asm.MovRM X86.Asm.RAX (X86.Asm.MBase X86.Asm.R10 (0 - pt)),
        X86.Asm.MovRR X86.Asm.RDX X86.Asm.RAX ] ++ part X86.Asm.RDX HeapObj.Header.ClosureFilled ++
      [ X86.Asm.MovRI X86.Asm.RSI (HeapObj.Header.partUnit HeapObj.Header.ClosureFilled),
        X86.Asm.Alu X86.Asm.ADD X86.Asm.RAX X86.Asm.RSI,
        X86.Asm.MovMR (X86.Asm.MBase X86.Asm.RDI 0) X86.Asm.RAX   -- one more filled
      , X86.Asm.MovRM X86.Asm.RAX (X86.Asm.MBase X86.Asm.R10 (8 - pt)),
        X86.Asm.MovMR (X86.Asm.MBase X86.Asm.RDI 8) X86.Asm.RAX           -- code
      , X86.Asm.Lea X86.Asm.RSI (X86.Asm.MBase X86.Asm.R10 (16 - pt)),
        X86.Asm.Lea X86.Asm.RCX (X86.Asm.MBase X86.Asm.RDI 16)
      , X86.Asm.Lbl pcopy, X86.Asm.Test X86.Asm.RDX X86.Asm.RDX, X86.Asm.Jcc X86.Asm.E pdone
      , X86.Asm.MovRM X86.Asm.RAX (X86.Asm.MBase X86.Asm.RSI 0), X86.Asm.MovMR (X86.Asm.MBase X86.Asm.RCX 0) X86.Asm.RAX
      , X86.Asm.AluI X86.Asm.ADD X86.Asm.RSI 8, X86.Asm.AluI X86.Asm.ADD X86.Asm.RCX 8,
        X86.Asm.AluI X86.Asm.SUB X86.Asm.RDX 1, X86.Asm.Jmp pcopy
      , X86.Asm.Lbl pdone, X86.Asm.MovMR (X86.Asm.MBase X86.Asm.RCX 0) X86.Asm.R11
      , toPointer X86.Asm.RAX X86.Asm.RDI,
        X86.Asm.JmpM (X86.Asm.MBase X86.Asm.R12 (0 - pt))     -- the new closure's pointer word
      -- the slow path: root the closure and the argument across it
      , X86.Asm.Lbl slow
      , X86.Asm.Lea X86.Asm.RSI (X86.Asm.MRip (Linkage.Sym.symLabel Linkage.Sym.SymNRoots) 0),
        X86.Asm.MovRM X86.Asm.RAX (X86.Asm.MBase X86.Asm.RSI 0)
      , X86.Asm.MovRR X86.Asm.RDX X86.Asm.RAX, X86.Asm.ShiftI X86.Asm.SHL X86.Asm.RDX (cast Area.rootShift),
        X86.Asm.Lea X86.Asm.RDI (X86.Asm.MRip (Linkage.Sym.symLabel Linkage.Sym.SymRoots) 0),
          X86.Asm.Alu X86.Asm.ADD X86.Asm.RDI X86.Asm.RDX
      , X86.Asm.MovMR (X86.Asm.MBase X86.Asm.RDI (root 0)) X86.Asm.R10,
        X86.Asm.MovMR (X86.Asm.MBase X86.Asm.RDI (root 1)) X86.Asm.R11
      , X86.Asm.AluI X86.Asm.ADD X86.Asm.RAX 2, X86.Asm.MovMR (X86.Asm.MBase X86.Asm.RSI 0) X86.Asm.RAX
      , X86.Asm.MovRR X86.Asm.RDI X86.Asm.RCX, X86.Asm.Call (Linkage.Sym.symLabel Linkage.Sym.SymAllocSlow)
      , X86.Asm.Lea X86.Asm.RSI (X86.Asm.MRip (Linkage.Sym.symLabel Linkage.Sym.SymNRoots) 0),
        X86.Asm.MovRM X86.Asm.RDX (X86.Asm.MBase X86.Asm.RSI 0), X86.Asm.AluI X86.Asm.SUB X86.Asm.RDX 2,
          X86.Asm.MovMR (X86.Asm.MBase X86.Asm.RSI 0) X86.Asm.RDX
      , X86.Asm.ShiftI X86.Asm.SHL X86.Asm.RDX (cast Area.rootShift),
        X86.Asm.Lea X86.Asm.RCX (X86.Asm.MRip (Linkage.Sym.symLabel Linkage.Sym.SymRoots) 0),
          X86.Asm.Alu X86.Asm.ADD X86.Asm.RCX X86.Asm.RDX
      , X86.Asm.MovRM X86.Asm.R10 (X86.Asm.MBase X86.Asm.RCX (root 0)),
        X86.Asm.MovRM X86.Asm.R11 (X86.Asm.MBase X86.Asm.RCX (root 1))
      , X86.Asm.Jmp
        initClosure ]                                            -- the new space in rdi, the routine's result
      where
        ||| The pointer tag: the closure in r10 and the continuation in r12 are
        ||| pointer words, the closure allocated in rdi an address.
        pt : Int
        pt = cast (HeapObj.ValEnc.pointerTag venc)

        ||| Where the root buffer holds its entry `i`, as a displacement.
        root : Bits64 -> Int
        root i = cast (Area.rootOffset i)

        ||| The address in `s` as a pointer word in `d`.
        toPointer : (d, s : X86.Asm.Reg64) -> X86.Asm.Instr
        toPointer d s = if pt == 0 then X86.Asm.MovRR d s else X86.Asm.Lea d (X86.Asm.MBase s pt)

        nregs : Nat
        nregs = length abi.wordRegs

        -- Load the word registers that satisfy `which` from the staged
        -- arguments in SCRATCH, at r9.
        loads : (X86.Asm.Reg64 -> Bool) -> List X86.Asm.Instr
        loads which = [ X86.Asm.MovRM r (X86.Asm.MBase X86.Asm.R9 (cast (8 * i)))
                      | (i, r) <- zip [0 .. nregs] (map X86.Asm.regOfNum abi.wordRegs), which r ]

        ||| A part of the closure header in `rax`, extracted into a register.
        part : X86.Asm.Reg64 -> HeapObj.Header.HeaderPart HeapObj.Kind.CLOSURE -> List X86.Asm.Instr
        part r p = X86.Asm.extractField r (cast (fst (HeapObj.Header.place p))) (cast (snd (HeapObj.Header.place p)))

        -- local labels, below the program's
        extend, copy, copied, copyArgs, regs, initClosure, pcopy, pdone, slow : X86.Asm.Label
        extend = 40
        copy = 41
        copied = 42
        copyArgs = 43
        regs = 44
        initClosure = 45
        pcopy = 46
        pdone = 47
        slow = 48

------------------------------------------------------------------------------
-- Data: rodata (HALT and the messages) and the bss areas

||| The seed's read-only data, given the text labels (HALT's code word is the
||| address of `idris_halt`), with each symbol's offset. HALT comes first, at
||| offset 0 of the 16-aligned section.
export
seedRodata : (textLabels : SortedMap X86.Asm.Label Int) -> (List Bits8, List (Linkage.Sym, Int))
seedRodata tl =
  let haltCode = fromMaybe 0 (lookup (Linkage.Sym.symLabel Linkage.Sym.SymHalt) tl)
      halt = Bytes.le64 (cast haltCode) ++ Bytes.le64 0            -- code, parent
      m1 = Bytes.pad8 msgUnsupported
      m3 = Bytes.pad8 msgStackOverflow
  in ( halt ++ m1 ++ m3
     , [ (Linkage.Sym.SymHALT, 0)
       , (Linkage.Sym.SymMsgUnsupported, cast (length halt))
       , (Linkage.Sym.SymMsgStackOverflow, cast (length halt + length m1)) ] )

||| What the seed's own code needs: `idris_apply`'s slow path roots the
||| closure and its argument. What it stages for a closure is the program's
||| largest arity, which the program's areas cover.
export
seedAreas : Linkage.Areas
seedAreas = Linkage.MkAreas 0 2 0

||| The zero-initialised per-thread areas, 8-aligned, in bss: `ARGS`, then
||| `ROOTS`, `NROOTS`, `SCRATCH`, `STACK_LIMIT`, `ARGV` and `RUNTIME`.
export
seedBss : Linkage.Areas -> List (Linkage.Sym, Int)
seedBss a =
  let roots = 8 * cast a.args
      nroots = roots + 8 * cast a.roots
      limit = nroots + 8 + 8 * cast a.scratch
  in [ (Linkage.Sym.SymArgs, 0),
    (Linkage.Sym.SymRoots, roots), (Linkage.Sym.SymNRoots, nroots), (Linkage.Sym.SymScratch, nroots + 8),
      (Linkage.Sym.SymStackLimit, limit)
     , (Linkage.Sym.SymArgv, limit + 8), (Linkage.Sym.SymRuntime, limit + 16) ]

export
seedBssSize : Linkage.Areas -> Int
seedBssSize a = 8 * (cast (a.args + a.roots + 1 + a.scratch + 2) + cast Area.runtimeWords)
