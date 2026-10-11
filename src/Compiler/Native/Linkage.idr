||| What generated code, the runtime and the linker agree on: the runtime
||| contract, the image's symbols and their labels, the per-thread memory
||| areas, the shape of a resume point, and the parameters an image is built
||| with. Nothing here is code: the runtime's routines are the runtime
||| library's, the rest of the seed's are `Compiler.Native.Seed`, and
||| `Compiler.Native.Link` makes the image.
module Compiler.Native.Linkage

import public Compiler.Native.IRCommon
import Compiler.Native.X86.Asm

import Core.Name
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
symName SymAllocMutable = "idris_alloc_mutable"
symName SymStackLimit = "STACK_LIMIT"
symName SymStackOverflow = "idris_stack_overflow"
symName SymMsgStackOverflow = "msg_stack_overflow"

||| The first label a program may use for itself.
public export
reservedLabels : Label
reservedLabels = 64

------------------------------------------------------------------------------
-- The runtime contract
--
-- What generated code and the runtime may assume of each other is declared
-- here, not taken from the runtime's compilation, in both directions. The
-- routines are what the runtime provides: each reached by name or by
-- symbol, with its signature in the term IR; the lowering calls them as
-- declared, and the runtime library's flat forms are checked against the
-- declarations when a program is lowered. The intrinsics are what the
-- lowering provides to fragment code: `%extern` declarations of the runtime
-- library that the flat lowering turns into instructions; each is checked
-- against its declaration when the runtime is loaded. A routine or an
-- intrinsic that is missing or has another signature is an error of the
-- compilation. Code compiled to join a runtime that is already built
-- depends on the contract alone.

||| The name of the `Direct` function of a flat form, which a form's
||| function has: the name by which generated code calls a routine of the
||| runtime.
public export
flatName : Name -> Name
flatName n = NS (mkNamespace "_flat") n

||| A routine of the runtime that generated code reaches.
public export
record Routine (enc : Enc) where
  constructor MkRoutine
  ||| The function of the runtime library that is the routine; for one the
  ||| runtime does not have yet, the name its calls use.
  name : Name
  ||| Whether the runtime has it. A call of a routine it does not have ends
  ||| the program as `Unsupported` does.
  provided : Bool
  ||| The symbol by which the rendering and the seed reach it, if they do:
  ||| the rendering defines it at the routine's function.
  symbol : Maybe Sym
  results : List (Ty enc)
  params : List (Ty enc)

||| The routine that ends the process with a status.
public export
runtimeExit : Name
runtimeExit = NS (mkNamespace "Runtime.System") (UN (Basic "exit"))

||| The routine that writes a message to the standard error and ends the
||| process with status 1.
public export
runtimeCrash : Name
runtimeCrash = NS (mkNamespace "Runtime.System") (UN (Basic "crash"))

||| The routine for an `Integer` operation the fast paths leave to the
||| runtime, which has none yet.
public export
integerRoutine : String -> Name
integerRoutine op = UN (Basic ("idris_integer_" ++ op))

||| The routines, with their signatures.
export
routines : {enc : Enc} -> List (Routine enc)
routines =
  [ MkRoutine runtimeExit True Nothing [] [W64]
  , MkRoutine runtimeCrash True (Just SymCrash) [] [W64, W64]
  , integer "add" [Val] [Val, Val]
  , integer "sub" [Val] [Val, Val]
  , integer "mul" [Val] [Val, Val]
  , integer "and" [Val] [Val, Val]
  , integer "or" [Val] [Val, Val]
  , integer "xor" [Val] [Val, Val]
  , integer "div" [Val] [Val, Val]
  , integer "mod" [Val] [Val, Val]
  , integer "shl" [Val] [Val, Val]
  , integer "shr" [Val] [Val, Val]
  , integer "neg" [Val] [Val]
  , integer "compare" [W64] [Val, Val]
  , integer "to_bits64" [W64] [Val]
  , integer "from_int64" [Val] [W64]
  , integer "from_bits64" [Val] [W64] ]
  where
    integer : String -> List (Ty enc) -> List (Ty enc) -> Routine enc
    integer op rs ps = MkRoutine (integerRoutine op) False Nothing rs ps

||| The symbol the routine whose function has the name is reached by.
export
routineSymbol : {enc : Enc} -> Name -> Maybe Sym
routineSymbol n = do
  r <- find (\r => r.provided && flatName r.name == n) (routines {enc})
  r.symbol

||| The intrinsics: the `%extern` primitives of the runtime library that are
||| instructions, never calls, what the runtime is written with. Each takes
||| words and the token, which has no register, last, and returns the token
||| with its value, so that its effect is ordered among the others by data
||| dependence. A memory access is at a base address plus a byte offset; a
||| narrow load extends the bits with zeros.
public export
data Intrinsic
  = ||| A system call: its number and six arguments, then its result.
    Syscall6
  | ||| Load a word.
    Load64
  | ||| Load 8, 16 or 32 bits.
    LoadNarrow SubWord
  | ||| Store a word.
    Store64
  | ||| Store a word's low 8, 16 or 32 bits.
    StoreNarrow SubWord

||| An intrinsic as the runtime library declares it: the registers of its
||| arguments, the token among them taking none, and of its result.
public export
record IntrinsicSig (0 enc : Enc) where
  constructor MkIntrinsicSig
  name : Name
  intrinsic : Intrinsic
  params : List (Ty enc)
  results : List (Ty enc)

||| The intrinsics, with their signatures.
export
intrinsics : {0 enc : Enc} -> List (IntrinsicSig enc)
intrinsics =
  [ MkIntrinsicSig (system "prim__syscall6") Syscall6 (replicate 7 W64) [W64]
  , memory "prim__load64" Load64 [W64, W64] [W64]
  , memory "prim__load32" (LoadNarrow Sub32) [W64, W64] [W64]
  , memory "prim__load16" (LoadNarrow Sub16) [W64, W64] [W64]
  , memory "prim__load8" (LoadNarrow Sub8) [W64, W64] [W64]
  , memory "prim__store64" Store64 [W64, W64, W64] []
  , memory "prim__store32" (StoreNarrow Sub32) [W64, W64, W64] []
  , memory "prim__store16" (StoreNarrow Sub16) [W64, W64, W64] []
  , memory "prim__store8" (StoreNarrow Sub8) [W64, W64, W64] [] ]
  where
    system : String -> Name
    system n = NS (mkNamespace "Runtime.System") (UN (Basic n))

    memory : String -> Intrinsic -> List (Ty enc) -> List (Ty enc) -> IntrinsicSig enc
    memory n = MkIntrinsicSig (NS (mkNamespace "Runtime.Memory") (UN (Basic n)))

||| The intrinsic a primitive of the runtime library is, by its name.
export
intrinsicOf : {0 enc : Enc} -> Name -> Maybe Intrinsic
intrinsicOf n = (.intrinsic) <$> find (\i => i.name == n) (intrinsics {enc})

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
