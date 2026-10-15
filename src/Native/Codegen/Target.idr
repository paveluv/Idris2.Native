||| The target: how the machine's registers are numbered and named, how values
||| pass between functions (`Abi`), and which registers are reserved so that
||| register allocation never uses them.
||| Only the parameters the IR needs so far are here; the rendering will add
||| its own, such as how a 64-bit constant or a code address is
||| materialised. Each target's values live with its rendering:
||| `Native.Codegen.X86.Target`.
|||
||| Register roles, on every target:
|||
||| * A call's arguments, and a `Direct` function's results, travel as the
|||   target's `Abi` places them (`place`): in its word and floating-point
|||   argument registers, then in the per-thread `ARGS` area, never on the
|||   machine stack. A CPS function's `Return` delivers its one value in the
|||   return register.
||| * The allocation window, `hp` and `hplim`, is pinned in two registers,
|||   and under the heap lowering the current continuation, `k`, in a third.
|||   Pinned registers are global state: never allocated, saved or restored,
|||   and read and written only by the allocation fast path and the
|||   intrinsics. Because no prologue saves them, a write by a runtime routine
|||   persists into its caller: that is how the collector publishes a new
|||   allocation window or a moved continuation.
||| * Every other register is scratch: there are no callee-saved registers.
|||   A moving collector must update every live reference, and references in
|||   the registers of suspended calls could not be found without a register
|||   map for every call site. Instead every value that must survive a call
|||   is stored where the collector already looks: in the continuation, in
|||   the frame, or in the root buffer `ROOTS`. This buys a root set with no
|||   maps and a register allocator with no callee-save trade-off.
|||
||| The pinned registers must be ones the platform's C convention preserves,
||| so that code following that convention leaves them intact.
module Native.Codegen.Target

%default total

||| A hardware register, by the target's own numbering (on x86-64, the
||| encoding number).
public export
TargetReg : Type
TargetReg = Nat

||| A floating-point register, by the target's own numbering (on x86-64, the
||| xmm register's number).
public export
FloatReg : Type
FloatReg = Nat

||| The register class a value crosses a call boundary in: an `F64` in a
||| floating-point register, every other value in a word register.
public export
data RegClass = WordClass | FloatClass

||| Where one value of a call's arguments or of a `Direct` function's results
||| travels.
public export
data Loc
  = ||| A word argument register.
    InWordReg TargetReg
  | ||| A floating-point argument register.
    InFloatReg FloatReg
  | ||| Word n of the per-thread `ARGS` area.
    InArgs Nat

public export
Show Loc where
  show (InWordReg r) = "word register " ++ show r
  show (InFloatReg r) = "float register " ++ show r
  show (InArgs n) = "ARGS word " ++ show n

||| How values pass between functions: a call's arguments, a `Direct`
||| function's results, and what `idris_apply` passes on. The convention is
||| the project's own, so it is a value here rather than constants in the
||| rendering and the seed: every place that passes values asks `place`.
public export
record Abi where
  constructor MkAbi
  ||| The word registers that carry word values, in order.
  wordRegs : List TargetReg
  ||| The floating-point registers that carry `F64` values, in order.
  floatRegs : List FloatReg

||| Where each of a list of values goes, in order: each class takes its own
||| registers in turn, and a value whose class has run out takes the next
||| word of `ARGS`, one word each, in the order of the values. Arguments and
||| results both go where this places them: a return passes values as a call
||| does.
public export
place : Abi -> List RegClass -> List Loc
place abi = go abi.wordRegs abi.floatRegs 0
  where
    go : List TargetReg -> List FloatReg -> Nat -> List RegClass -> List Loc
    go _ _ _ [] = []
    go ws fs n (WordClass :: cs) = case ws of
      w :: ws' => InWordReg w :: go ws' fs n cs
      [] => InArgs n :: go [] fs (S n) cs
    go ws fs n (FloatClass :: cs) = case fs of
      f :: fs' => InFloatReg f :: go ws fs' n cs
      [] => InArgs n :: go ws [] (S n) cs

||| The words of `ARGS` that values of these classes take.
public export
argsWords : Abi -> List RegClass -> Nat
argsWords abi cs = length (filter inArgs (place abi cs))
  where
    inArgs : Loc -> Bool
    inArgs (InArgs _) = True
    inArgs _ = False

||| How Idris-level continuations are realised. It decides whether `k` is
||| pinned.
public export
data Lowering
  = ||| Continuations are heap objects (`CONT`): a non-tail call allocates one
    ||| holding the resume address and the live values, every transfer of
    ||| control is a jump, and `k` holds the current continuation. The active
    ||| lowering.
    HeapLowering
  | ||| Continuations are frames on a machine stack, found by the collector
    ||| through stack maps. Kept consistent with the IR so that the backend
    ||| can switch to it, but not implemented.
    StackLowering

public export
Eq Lowering where
  HeapLowering == HeapLowering = True
  StackLowering == StackLowering = True
  _ == _ = False

public export
record Target where
  constructor MkTarget
  ||| A name, for messages.
  name : String
  ||| Bytes per word: 8 on every target in scope.
  wordSize : Nat
  ||| How continuations are realised.
  lowering : Lowering
  ||| How values pass between functions.
  abi : Abi
  ||| The register a CPS function's `Return` delivers its value in.
  returnReg : TargetReg
  ||| The allocation pointer: the next free byte of the allocation window.
  ||| Pinned under every lowering.
  hp : TargetReg
  ||| The allocation limit: the end of the allocation window. Pinned under
  ||| every lowering.
  hplim : TargetReg
  ||| The continuation register, holding the current continuation. Pinned
  ||| under the heap lowering only; scratch otherwise.
  k : TargetReg
  ||| The machine stack pointer. Generated code never moves it.
  stackPointer : TargetReg
  ||| Register names, for dumps and messages.
  regName : TargetReg -> String

||| The registers register allocation may never use: the pinned ones and the
||| stack pointer.
export
reserved : Target -> List TargetReg
reserved t =
  [t.hp, t.hplim, t.stackPointer] ++ (if t.lowering == HeapLowering then [t.k] else [])
