||| The image's symbols (`Sym`) and their labels: the seed owns the labels
||| below `reservedLabels`, and lowered code numbers its own from there.
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Native.Codegen.Linkage.Routine` says what it is).
module Native.Codegen.Linkage.Sym

import Native.Codegen.IRCommon.Area as IRCommon
import Native.Codegen.X86.Asm

%default total

public export
data Sym
  = SymStart           -- `_start`: the ELF entry point
  | SymMain            -- the program's entry under the heap lowering; the caller of `link` defines it
  | SymHalt            -- `idris_halt`: the code of the HALT continuation; result in rax -> exit_group
  | SymCrash           -- `idris_crash(msg, len)`: write to fd 2, exit_group(1)
  | SymUnsupported     -- `idris_unsupported`: the abort stub for unlowered code; writes a message, exit_group(70)
  | SymAllocSlow       -- `idris_alloc_slow(n)`: the allocation slow path, the runtime's
  | SymHALT            -- rodata: the static HALT continuation, the bottom of every continuation chain
  | SymMsgUnsupported  -- rodata
  | SymArgs            -- bss: ARGS, sized by `Areas`: arguments beyond the argument registers
  | SymRoots           -- bss: ROOTS, sized by `Areas`: the root buffer of the rooting stubs
  | SymNRoots          -- bss: NROOTS, 1 word: the entries of ROOTS in use
  | SymScratch         -- bss: SCRATCH, sized by `Areas`: extra registers for register allocation
  | SymApply           -- `idris_apply(f, a)`: apply a closure to one argument (CPS)
  | SymAllocMutable    -- `idris_alloc_mutable(n)`: the only way a mutable object is allocated, the runtime's
  | SymStackLimit      -- bss: STACK_LIMIT, 1 word: the lowest the stack pointer may go in direct code
  | SymStackOverflow   -- `idris_stack_overflow`: where direct code's stack check fails; message, exit 1
  | SymMsgStackOverflow  -- rodata
  | SymArgv            -- bss: ARGV, 1 word: the stack pointer at entry
  | SymRuntimeStart    -- `idris_start(entry, window)`: the runtime's start-up, which `_start` calls
  | SymRuntime         -- bss: RUNTIME, `runtimeWords` words: the runtime's state

public export
symLabel : Sym -> X86.Asm.Label
symLabel SymStart = 0
symLabel SymMain = 1
symLabel SymHalt = 2
symLabel SymCrash = 3
symLabel SymUnsupported = 4
symLabel SymAllocSlow = 5
symLabel SymHALT = 7
symLabel SymMsgUnsupported = 8
symLabel SymArgs = 10
symLabel SymRoots = 11
symLabel SymNRoots = 12
symLabel SymScratch = 13
symLabel SymApply = 14
symLabel SymAllocMutable = 16
symLabel SymStackLimit = 17
symLabel SymStackOverflow = 18
symLabel SymMsgStackOverflow = 19
symLabel SymArgv = 20
symLabel SymRuntimeStart = 21
symLabel SymRuntime = 22

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
symName SymMsgUnsupported = "msg_unsupported"
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

||| The symbol of a per-thread area.
public export
areaSym : IRCommon.Area -> Sym
areaSym IRCommon.Area.ARGS = SymArgs
areaSym IRCommon.Area.ROOTS = SymRoots
areaSym IRCommon.Area.NROOTS = SymNRoots
areaSym IRCommon.Area.SCRATCH = SymScratch
areaSym IRCommon.Area.STACK_LIMIT = SymStackLimit
areaSym IRCommon.Area.ARGV = SymArgv
areaSym IRCommon.Area.RUNTIME = SymRuntime

||| The first label a program may use for itself.
public export
reservedLabels : X86.Asm.Label
reservedLabels = 64
