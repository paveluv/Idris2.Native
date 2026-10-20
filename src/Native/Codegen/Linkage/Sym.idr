||| The image's symbols (`Sym`) and their labels: the seed owns the labels
||| below `reservedLabels`, and lowered code numbers its own from there.
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Native.Codegen.Linkage.Routine` says what it is).
module Native.Codegen.Linkage.Sym

import Native.Area
import Native.Codegen.X86.Asm

%default total

public export
data Sym
  = ||| `_start`: the ELF entry point
    SymStart
  | ||| the program's entry under the heap lowering; the caller of `link`
    ||| defines it
    SymMain
  | ||| `idris_halt`: the code of the HALT continuation; result in rax ->
    ||| exit_group
    SymHalt
  | ||| `idris_crash(msg, len)`: write to fd 2, exit_group(1)
    SymCrash
  | ||| `idris_unsupported(msg, len)`: the abort stub for unlowered code;
    ||| write to fd 2, exit_group(70)
    SymUnsupported
  | ||| `idris_alloc_slow(n)`: the allocation slow path, the runtime's
    SymAllocSlow
  | ||| rodata: the static HALT continuation, the bottom of every
    ||| continuation chain
    SymHALT
  | ||| bss: ARGS, sized by `Areas`: arguments beyond the argument registers
    SymArgs
  | ||| bss: ROOTS, sized by `Areas`: the root buffer of the rooting stubs
    SymRoots
  | ||| bss: NROOTS, 1 word: the entries of ROOTS in use
    SymNRoots
  | ||| bss: SCRATCH, sized by `Areas`: extra registers for register
    ||| allocation
    SymScratch
  | ||| `idris_apply(f, a)`: apply a closure to one argument (CPS)
    SymApply
  | ||| `idris_alloc_mutable(n)`: the only way a mutable object is
    ||| allocated, the runtime's
    SymAllocMutable
  | ||| bss: STACK_LIMIT, 1 word: the lowest the stack pointer may go in
    ||| direct code
    SymStackLimit
  | ||| `idris_stack_overflow`: where direct code's stack check fails;
    ||| message, exit 1
    SymStackOverflow
  | ||| rodata
    SymMsgStackOverflow
  | ||| bss: ARGV, 1 word: the stack pointer at entry
    SymArgv
  | ||| `idris_start(entry, window)`: the runtime's start-up, which `_start`
    ||| calls
    SymRuntimeStart
  | ||| bss: RUNTIME, `runtimeWords` words: the runtime's state
    SymRuntime
  | ||| bss: CONSTANTS, sized by `Areas`: the program's top-level constants
    SymConstants

public export
label : Sym -> X86.Asm.Label
label SymStart = 0
label SymMain = 1
label SymHalt = 2
label SymCrash = 3
label SymUnsupported = 4
label SymAllocSlow = 5
label SymHALT = 7
label SymArgs = 10
label SymRoots = 11
label SymNRoots = 12
label SymScratch = 13
label SymApply = 14
label SymAllocMutable = 16
label SymStackLimit = 17
label SymStackOverflow = 18
label SymMsgStackOverflow = 19
label SymArgv = 20
label SymRuntimeStart = 21
label SymRuntime = 22
label SymConstants = 23

||| Names as the ABI documents write them (for dumps).
public export
symName : Sym -> String
symName SymStart = "_start"
symName SymMain = "main"
symName SymHalt = "idris_halt"
symName SymCrash = "idris_crash"
symName SymUnsupported = "idris_unsupported"
symName SymAllocSlow = "idris_alloc_slow"
symName SymHALT = "HALT"
symName SymArgs = "ARGS"
symName SymRoots = "ROOTS"
symName SymNRoots = "NROOTS"
symName SymScratch = "SCRATCH"
symName SymApply = "idris_apply"
symName SymAllocMutable = "idris_alloc_mutable"
symName SymStackLimit = "STACK_LIMIT"
symName SymStackOverflow = "idris_stack_overflow"
symName SymMsgStackOverflow = "msg_stack_overflow"
symName SymArgv = "ARGV"
symName SymRuntimeStart = "idris_start"
symName SymRuntime = "RUNTIME"
symName SymConstants = "CONSTANTS"

||| The symbol of an area.
public export
areaSym : Area -> Sym
areaSym Area.ARGS = SymArgs
areaSym Area.ROOTS = SymRoots
areaSym Area.NROOTS = SymNRoots
areaSym Area.SCRATCH = SymScratch
areaSym Area.STACK_LIMIT = SymStackLimit
areaSym Area.ARGV = SymArgv
areaSym Area.RUNTIME = SymRuntime
areaSym Area.CONSTANTS = SymConstants

||| The first label a program may use for itself.
public export
reservedLabels : X86.Asm.Label
reservedLabels = 64
