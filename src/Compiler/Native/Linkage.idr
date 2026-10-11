||| What generated code, the runtime seed and the linker agree on: the
||| image's symbols and their labels, the per-thread memory areas, the shape
||| of a resume point, and the parameters an image is built with. Nothing
||| here is code: the seed's routines are `Compiler.Native.Seed`, and
||| `Compiler.Native.Link` makes the image.
module Compiler.Native.Linkage

import Compiler.Native.X86.Asm

import Data.List

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

||| A 16-aligned code label preceded by its layout word, as every resume
||| point and `idris_halt` need: pad to 8 mod 16, the word, the label.
export
resumePoint : Label -> (layout : Integer) -> List Instr
resumePoint l w = [Align 16, Bytes (replicate 8 0xCC), Quad w, Lbl l]

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
