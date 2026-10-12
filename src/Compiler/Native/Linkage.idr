||| What generated code, the runtime and the linker agree on: the runtime
||| contract, the image's symbols and their labels, the per-thread memory
||| areas, the shape of a resume point, and the parameters an image is built
||| with. Nothing here is code: the runtime's routines are the runtime
||| library's, the rest of the seed's are `Compiler.Native.Seed`, and
||| `Compiler.Native.Link` makes the image.
module Compiler.Native.Linkage

import Compiler.Native.HeapObject
import Compiler.Native.IRCommon
import Compiler.Native.Platform
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
symLabel : Sym -> Label
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
areaSym : Area -> Sym
areaSym ARGS = SymArgs
areaSym ROOTS = SymRoots
areaSym NROOTS = SymNRoots
areaSym SCRATCH = SymScratch
areaSym STACK_LIMIT = SymStackLimit
areaSym ARGV = SymArgv
areaSym RUNTIME = SymRuntime

||| Whether a function may convert between words and addresses in the term
||| IR: only the functions of the module that implements the runtime's
||| memory, where an address is made from a word and taken apart.
public export
convertsIn : Name -> Bool
convertsIn (NS ns _) = ns == mkNamespace "Runtime.Memory"
convertsIn _ = False

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
-- compilation. The OS services are what an operating system provides to
-- the rest of the runtime: `%extern` declarations of the generic runtime,
-- each bound, for the platform a program is compiled for, to a function of
-- that platform's module, which the flat lowering calls in its place; the
-- declarations are checked when the runtime is loaded, and the functions
-- when a program is lowered. Code compiled to join a runtime that is
-- already built depends on the contract alone.

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

||| The routine that starts the program, before `main`: the stack limit, the
||| first allocation window, the arguments.
public export
runtimeStart : Name
runtimeStart = NS (mkNamespace "Runtime.Start") (UN (Basic "start"))

||| The allocation slow path: `bytes` in, the space of an object out, with
||| the window moved past it; it collects when the heap has grown enough.
public export
runtimeAllocSlow : Name
runtimeAllocSlow = NS (mkNamespace "Runtime.Space") (UN (Basic "allocSlow"))

||| The allocation of a mutable object, which is never inline: `bytes` in,
||| the object's space out.
public export
runtimeAllocMutable : Name
runtimeAllocMutable = NS (mkNamespace "Runtime.Space") (UN (Basic "allocMutable"))

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

||| The runtime's module that lays strings out under the encoding: the one
||| module of the runtime that reads a string's header or bytes. Every other
||| part of the runtime asks it. None yet for UTF-32.
export
stringModule : StringEncoding -> Maybe Namespace
stringModule Utf8 = Just (mkNamespace "Runtime.String.Utf8")
stringModule Utf32 = Nothing

||| A string routine under the encoding: the string module's function of the
||| operation's name, and whether the runtime has it.
stringFunction : StringEncoding -> String -> (Name, Bool)
stringFunction e op = case stringModule e of
  Just ns => (NS ns (UN (Basic op)), True)
  Nothing => (UN (Basic ("idris_string_" ++ op)), False)

||| The name generated code calls a string routine by.
export
stringRoutine : Enc -> String -> Name
stringRoutine enc op = case stringFunction enc.strings op of
  (n, True) => flatName n
  (n, False) => n

||| The routines, with their signatures. The string routines are the eight
||| primitive operations on strings and their comparison (-1, 0 or 1), over
||| strings as ordinary code holds them; a character is its code point, a
||| count or an index a word.
export
routines : {enc : Enc} -> List (Routine enc)
routines =
  [ string "length" [W64] [Val]
  , string "head" [W64] [Val]
  , string "tail" [Val] [Val]
  , string "index" [W64] [Val, W64]
  , string "cons" [Val] [W64, Val]
  , string "append" [Val] [Val, Val]
  , string "reverse" [Val] [Val]
  , string "substr" [Val] [W64, W64, Val]
  , string "compare" [W64] [Val, Val]
  , MkRoutine runtimeStart True (Just SymRuntimeStart) [] [W64, W64]
  , MkRoutine runtimeAllocSlow True (Just SymAllocSlow) [W64] [W64]
  , MkRoutine runtimeAllocMutable True (Just SymAllocMutable) [W64] [W64]
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

    string : String -> List (Ty enc) -> List (Ty enc) -> Routine enc
    string op rs ps = let (n, p) = stringFunction enc.strings op in MkRoutine n p Nothing rs ps

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
  | ||| The allocation pointer.
    GetHp
  | ||| Set the allocation pointer.
    SetHp
  | ||| The allocation limit.
    GetHpLim
  | ||| Set the allocation limit.
    SetHpLim
  | ||| The current continuation, as the pointer word it is.
    GetK
  | ||| Set the current continuation from a pointer word.
    SetK
  | ||| The pointer tag of the program's encoding: what a pointer word is
    ||| beyond the object's address.
    PointerTag
  | ||| The address of a per-thread area.
    AreaAddress Area
  | ||| The pointer word of a uniform value known to be an object of the kind.
    ObjectWord Kind
  | ||| The uniform value of a pointer word to an object of the kind.
    WordObject Kind

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
  [ MkIntrinsicSig (NS (mkNamespace "Runtime.OS.Syscall") (UN (Basic "prim__syscall6"))) Syscall6 (replicate 7 W64) [W64]
  , memory "prim__load64" Load64 [W64, W64] [W64]
  , memory "prim__load32" (LoadNarrow Sub32) [W64, W64] [W64]
  , memory "prim__load16" (LoadNarrow Sub16) [W64, W64] [W64]
  , memory "prim__load8" (LoadNarrow Sub8) [W64, W64] [W64]
  , memory "prim__store64" Store64 [W64, W64, W64] []
  , memory "prim__store32" (StoreNarrow Sub32) [W64, W64, W64] []
  , memory "prim__store16" (StoreNarrow Sub16) [W64, W64, W64] []
  , memory "prim__store8" (StoreNarrow Sub8) [W64, W64, W64] []
  , memory "prim__getHp" GetHp [] [W64]
  , memory "prim__setHp" SetHp [W64] []
  , memory "prim__getHpLim" GetHpLim [] [W64]
  , memory "prim__setHpLim" SetHpLim [W64] []
  , memory "prim__getK" GetK [] [W64]
  , memory "prim__setK" SetK [W64] []
  , memory "prim__pointerTag" PointerTag [] [W64]
  , memory "prim__stackLimitArea" (AreaAddress STACK_LIMIT) [] [W64]
  , memory "prim__argvArea" (AreaAddress ARGV) [] [W64]
  , memory "prim__rootsArea" (AreaAddress ROOTS) [] [W64]
  , memory "prim__nrootsArea" (AreaAddress NROOTS) [] [W64]
  , memory "prim__runtimeArea" (AreaAddress RUNTIME) [] [W64]
  , memory "prim__stringWord" (ObjectWord STRING) [Val] [W64]
  , memory "prim__wordString" (WordObject STRING) [W64] [Val]
  , memory "prim__conWord" (ObjectWord CON) [Val] [W64]
  , memory "prim__wordCon" (WordObject CON) [W64] [Val] ]
  where
    memory : String -> Intrinsic -> List (Ty enc) -> List (Ty enc) -> IntrinsicSig enc
    memory n = MkIntrinsicSig (NS (mkNamespace "Runtime.Memory") (UN (Basic n)))

||| The intrinsic a primitive of the runtime library is, by its name.
export
intrinsicOf : {0 enc : Enc} -> Name -> Maybe Intrinsic
intrinsicOf n = (.intrinsic) <$> find (\i => i.name == n) (intrinsics {enc})

||| The foreign functions of the libraries a program uses, `prelude` and
||| `base`, that the runtime implements, each with the flat function that
||| does: of the same type position by position, so that the lowering gives
||| the foreign function the boundary to it, which converts each argument and
||| the result as their types say. Most are `Runtime.Foreign`'s, by the
||| foreign one's module path and name (`System.prim__exit` by
||| `Runtime.Foreign.System.prim__exit`); those that lay strings out are the
||| string module's, under the program's encoding. A foreign function is
||| bound by its Idris name, whatever names the library gives it for C or
||| Scheme; one not listed stays `Unsupported`.
export
foreignFunctions : Enc -> List (Name, Name)
foreignFunctions enc =
  [ mirrored (NS (mkNamespace "System") (UN (Basic "prim__exit"))) ]
  ++ maybe [] (\ns => map (\f => (NS (mkNamespace "Prelude.Types") (UN (Basic f)), NS ns (UN (Basic f))))
                          ["fastPack", "fastUnpack", "fastConcat"])
           (stringModule enc.strings)
  where
    mirrored : Name -> (Name, Name)
    mirrored n@(NS ns f) = (n, NS (mkNamespace ("Runtime.Foreign." ++ show ns)) f)
    mirrored n = (n, NS (mkNamespace "Runtime.Foreign") n)

||| An OS service: what the runtime asks of the operating system, by the
||| name of the generic runtime's `%extern` for it, `Runtime.OS.prim__os_`
||| and the service's own name, with the registers of its arguments, the
||| token among them taking none, and of its result. A platform's module
||| implements it as a function of the service's own name.
public export
record OSService (0 enc : Enc) where
  constructor MkOSService
  service : String
  params : List (Ty enc)
  results : List (Ty enc)

||| The OS services. A result that reports success is 1 for success and 0
||| for failure, so that the generic runtime decides what a failure means.
|||
||| * `exit status`: end the process.
||| * `write handle address bytes`: write the bytes to the standard handle
|||   (1 the output, 2 the errors); the bytes written.
||| * `reserve bytes`: reserve address space, readable by nothing, which no
|||   memory is committed to; its address, 0 if there is none.
||| * `commit address bytes`: make reserved whole pages readable and
|||   writable, and zero; success.
||| * `release address bytes`: give committed whole pages back and reserve
|||   them again.
||| * `stackLimit`: the most bytes the process's stack may grow to, 0 if the
|||   system does not say.
||| * `pageBytes`: the system's page, the bytes memory is committed and
|||   released by.
export
osServices : {0 enc : Enc} -> List (OSService enc)
osServices =
  [ MkOSService "exit" [W64] []
  , MkOSService "write" [W64, W64, W64] [W64]
  , MkOSService "reserve" [W64] [W64]
  , MkOSService "commit" [W64, W64] [W64]
  , MkOSService "release" [W64, W64] []
  , MkOSService "stackLimit" [] [W64]
  , MkOSService "pageBytes" [] [W64] ]

||| The generic runtime's `%extern` for a service.
export
serviceExtern : OSService enc -> Name
serviceExtern s = NS (mkNamespace "Runtime.OS") (UN (Basic ("prim__os_" ++ s.service)))

||| The module of the runtime that implements the OS services on a platform,
||| if the platform is built.
export
platformModule : Platform -> Maybe Namespace
platformModule (MkPlatform X86_64 Linux) = Just (mkNamespace "Runtime.OS.LinuxX86_64")
platformModule _ = Nothing

||| The function that implements a service on the platform.
export
serviceFunction : Platform -> OSService enc -> Maybe Name
serviceFunction p s = (\ns => NS ns (UN (Basic s.service))) <$> platformModule p

||| Each service's extern bound to its function on the platform.
export
serviceBindings : {0 enc : Enc} -> Platform -> List (Name, Name)
serviceBindings p = mapMaybe (\s => (serviceExtern s,) <$> serviceFunction p s) (osServices {enc})

------------------------------------------------------------------------------
-- Parameters

||| The default allocation window: 4 MiB, the bytes the inline bump may
||| allocate before the runtime's slow path runs, which extends the window
||| or collects. A tiny window, chosen with `linkWith` or the directive
||| `nursery=`, makes tests take the slow path, and collect, often.
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
