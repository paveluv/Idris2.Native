||| The rendering of the IR as x86-64 instructions, under the heap lowering of
||| continuations.
|||
||| Registers. Every IR register is a `SCRATCH` slot (`Compiler.Native.LocatedIR.Reg`);
||| `rbx` holds `SCRATCH`'s address, so slot n is `[rbx + 8n]`, and is set at
||| every function entry, every resume point and after every runtime call,
||| since no register survives a transfer or a direct call. An instruction
||| loads its operands into `rax`, `rcx` and `rdx` and stores its result back.
||| `r15` and `r14` are the allocation window and `r12` the current
||| continuation, as `Compiler.Native.X86.Target.x86_64` pins them.
|||
||| Calls. Arguments travel where the target's `Abi` places them
||| (`Compiler.Native.Target.place`): words in rdi, rsi, rdx, rcx, r8 and r9,
||| `F64`s in xmm0 to xmm7, and the rest in `ARGS`; a function's prologue
||| stores them in its parameters' slots. An `F64` in a slot or in `ARGS` is
||| its bits. A tail call moves the arguments and jumps. A non-tail
||| call first allocates its continuation, 16 + 8 * |live| bytes: the resume
||| point's address, the parent (r12), then the live GC-visible values, then
||| the live raw ones; it sets r12 to it and jumps. A resume point is
||| 16-aligned and preceded by its layout word (`layoutWord`); it reloads the
||| live values, sets r12 to the parent and stores the result from rax. A
||| return puts the value in rax and jumps through r12. An application, tail
||| or not, goes through the runtime's `idris_apply`.
|||
||| Direct functions. A direct call saves what is live, passes the arguments
||| as a call does and executes a machine call; the callee's `Ret` passes its
||| results where `place` puts arguments, and the caller stores them in its
||| result registers' slots, `ARGS` first emptied, before restoring what it
||| saved. A Direct function keeps the stack 16-aligned inside it by
||| lowering it by a word on entry, since the call pushed one, and raising it
||| again before it returns. On entry it also compares the stack pointer
||| with the limit the seed sets at start-up (`STACK_LIMIT`), and below it
||| ends the program with a message, so that deep recursion in direct code
||| is reported rather than a fault.
|||
||| Allocation. An object or a continuation is a bump of r15 checked against
||| r14; the slow path, placed after the function, saves what is live across
||| it (the GC-visible values in `ROOTS`, the raw ones on the stack, kept
||| 16-aligned, since `SCRATCH` is dead across the call), calls
||| `idris_alloc_slow`, restores them, and rejoins the initialisation. A
||| direct call that cannot collect saves what is live on the stack alone.
|||
||| Areas. The rendering records the most of each per-thread area its code
||| uses: the arguments and results passed in `ARGS`, the entries of a rooting
||| stub in `ROOTS`, the slots in `SCRATCH`, and the largest arity
||| `idris_apply` can stage. The image's areas get exactly those sizes
||| (`Areas` in `Compiler.Native.Seed`), so no code writes past one.
|||
||| Invariants this rendering keeps: r12 holds a complete continuation at
||| every point where a collection can start and at every transfer; every
||| value live across a non-tail call is in the continuation it allocated,
||| and every value live across a tail call is an argument; and a
||| continuation is fully initialised before r12 is set to it, so no
||| collection can see a partial one.
module Compiler.Native.X86.Render

import Compiler.Native.Bytes
import Compiler.Native.HeapObject.Enc
import Compiler.Native.HeapObject.Header as HeapObject
import Compiler.Native.HeapObject.Kind
import Compiler.Native.HeapObject.LayoutWord
import Compiler.Native.HeapObject.ValEnc
import Compiler.Native.IRCommon.Conv
import Compiler.Native.IRCommon.Intrinsic as IRCommon
import Compiler.Native.IRCommon.Operators.ArithOp as Operators
import Compiler.Native.IRCommon.Operators.ConvOp
import Compiler.Native.IRCommon.Operators.FOp
import Compiler.Native.IRCommon.Operators.Rel
import Compiler.Native.IRCommon.Operators.SubWord
import Compiler.Native.IRCommon.Operators.UnOp
import Compiler.Native.IRCommon.Ty
import Compiler.Native.Linkage.Areas
import Compiler.Native.Linkage.ResumePoint
import Compiler.Native.Linkage.Routine
import Compiler.Native.Linkage.Sym
import Compiler.Native.LocatedIR.Block
import Compiler.Native.LocatedIR.Cont
import Compiler.Native.LocatedIR.Function
import Compiler.Native.LocatedIR.Instr as LocatedIR
import Compiler.Native.LocatedIR.Label as LocatedIR
import Compiler.Native.LocatedIR.Mem as LocatedIR
import Compiler.Native.LocatedIR.Opnd
import Compiler.Native.LocatedIR.Program
import Compiler.Native.LocatedIR.Reg
import Compiler.Native.LocatedIR.Static
import Compiler.Native.LocatedIR.Terminator as LocatedIR
import Compiler.Native.Target as Native
import Compiler.Native.X86.Asm as X86
import Compiler.Native.X86.Target
import Control.Monad.State.Interface
import Control.Monad.State.State
import Control.Monad.Trans
import Core.Name
import Data.Builder
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.Zippable

%default covering

||| What the rendering gives the linker: the program's code, which defines the
||| seed's `main` label, its read-only data, and the per-thread areas its code
||| uses.
public export
record Rendered where
  constructor MkRendered
  text : List X86.Instr
  rodata : List (X86.Label, List Bits8)
  areas : Areas

record RS (enc : Enc) where
  constructor MkRS
  nextLabel : Nat
  funs : SortedMap Name X86.Label
  ||| Each function's parameter types: an immediate argument for a `Val` or a
  ||| `Fix` parameter is an integer, whose word the value encoding gives.
  params : SortedMap Name (List (Ty enc))
  statics : SortedMap Name X86.Label
  ||| The code so far, accumulating at its end.
  text : SnocList X86.Instr
  ||| Slow paths, placed after the function being rendered.
  cold : SnocList X86.Instr
  rodata : SnocList (X86.Label, List Bits8)
  ||| The most of each per-thread area the code so far uses.
  areas : Areas

Render : Enc -> Type -> Type
Render enc = StateT (RS enc) (Either String)

failWith : String -> Render enc a
failWith = lift . Left

emit : X86.Instr -> Render enc ()
emit i = modify { text $= (:< i) }

emits : List X86.Instr -> Render enc ()
emits = traverse_ emit

coldEmit : X86.Instr -> Render enc ()
coldEmit i = modify { cold $= (:< i) }

||| Record that the code uses at least these areas.
uses : Areas -> Render enc ()
uses a = modify { areas $= maxAreas a }

fresh : Render enc X86.Label
fresh = do
  s <- get
  put ({ nextLabel := S s.nextLabel } s)
  pure s.nextLabel

sym : Sym -> X86.Label
sym = symLabel

-- Everything below renders for the program's encodings. The value encoding
-- decides how a `Val` immediate and a fixnum are words, and the pointer tag
-- every access through a pointer folds into its displacement.

parameters (enc : Enc)
  ------------------------------------------------------------------------------
  -- Operands

  reg64 : TargetReg -> Reg64
  reg64 = regOfNum

  xmm : FloatReg -> Xmm
  xmm = xmmOfNum

  abi : Abi
  abi = x86_64.abi

  ||| Where values of the types travel between functions.
  placeTys : List (Ty enc) -> List Native.Loc
  placeTys tys = Native.place abi (map classOf tys)

  ||| The type of an operand: its register's, or a word for an immediate.
  opTy : Opnd enc -> Ty enc
  opTy (R r) = regTy r
  opTy (Imm _) = W64
  opTy (StaticRef _) = Val

  ||| The register's slot, recorded as used.
  useSlot : Reg enc -> Render enc Nat
  useSlot r = do let n = slotOf r
                 uses (MkAreas 0 0 (S n))
                 pure n

  slotMem : Nat -> X86.Mem
  slotMem n = MBase RBX (cast (8 * n))

  staticLabel : Name -> Render enc X86.Label
  staticLabel n = do
    s <- get
    case lookup n s.statics of
      Just l => pure l
      Nothing => failWith ("no static " ++ show n)

  ||| The pointer tag of the value encoding: a pointer word is the object's address
  ||| plus it, so every load and store through a pointer folds its negation
  ||| into the displacement.
  ptag : Int
  ptag = cast (pointerTag enc.val)

  ||| The word of an immediate where a value of the type is expected: in a
  ||| `Val` or `Fix` position the immediate is an integer, and the value
  ||| encoding gives its word; elsewhere it is the word itself. The term's
  ||| immediates carry the proof that the value encoding has a word for them.
  immWord : Ty enc -> Int64 -> Integer
  immWord Val i = maybe (cast i) cast (valWord enc.val (cast i))
  immWord Fix i = maybe (cast i) cast (valWord enc.val (cast i))
  immWord _ i = cast i

  ||| Load an operand where a value of the type is expected.
  loadAs : Ty enc -> Reg64 -> Opnd enc -> Render enc ()
  loadAs t r (Imm i) = emit (MovRI r (immWord t i))
  loadAs _ r (StaticRef s) = do l <- staticLabel s; emit (Lea r (MRip l ptag))
  loadAs _ r (R x) = do n <- useSlot x; emit (MovRM r (slotMem n))

  ||| What a load or store through the register subtracts: the pointer tag if
  ||| the register holds a pointer word, nothing if it holds an address.
  baseTag : Reg enc -> Int
  baseTag r = if gcVisible (regTy r) then ptag else 0

  ||| Turn the object address in `s` into its pointer word in `d`.
  tagPointer : (d, s : Reg64) -> List X86.Instr
  tagPointer d s = if ptag == 0 then (if d == s then [] else [MovRR d s]) else [Lea d (MBase s ptag)]

  ||| Load a raw operand.
  load : Reg64 -> Opnd enc -> Render enc ()
  load = loadAs W64

  ||| The type two compared operands share: the register's, if either is one.
  pairTy : Opnd enc -> Opnd enc -> Ty enc
  pairTy (R x) _ = regTy x
  pairTy _ (R y) = regTy y
  pairTy (StaticRef _) _ = Val
  pairTy _ (StaticRef _) = Val
  pairTy _ _ = W64

  loadReg : Reg64 -> Reg enc -> Render enc ()
  loadReg r x = load r (R x)

  store : Reg enc -> Reg64 -> Render enc ()
  store d r = do n <- useSlot d; emit (MovMR (slotMem n) r)

  setBase : List X86.Instr
  setBase = [Lea RBX (MRip (sym SymScratch) 0)]

  cond : Rel -> Cond
  cond EqR = E
  cond NeR = NE
  cond LtS = L
  cond LeS = LE
  cond GtS = G
  cond GeS = GE
  cond LtU = B
  cond LeU = BE
  cond GtU = A
  cond GeU = AE

  fitsImm32 : Integer -> Bool
  fitsImm32 i = i >= -2147483648 && i <= 2147483647

  ||| Compare rax with the operand, where a value of the type is expected:
  ||| `test` against the word 0, an immediate compare where the word fits.
  compareWith : Ty enc -> Opnd enc -> Render enc ()
  compareWith t (Imm c) =
    let w = immWord t c in
    if w == 0 then emit (Test RAX RAX)
    else if fitsImm32 w then emit (AluI CMP RAX (cast w))
    else emits [MovRI RCX w, Alu CMP RAX RCX]
  compareWith _ (R y) = do loadReg RCX y; emit (Alu CMP RAX RCX)
  compareWith _ (StaticRef s) = do l <- staticLabel s; emits [Lea RCX (MRip l ptag), Alu CMP RAX RCX]

  ------------------------------------------------------------------------------
  -- Arithmetic

  ||| Arithmetic on raw words, into rax.
  wordArith : ArithOp -> Opnd enc -> Opnd enc ->
              (overflow : Maybe X86.Label) -> Render enc ()
  wordArith o x y ov = do
    load RAX x
    load RCX y
    case o of
      Add => emit (Alu ADD RAX RCX)
      Sub => emit (Alu SUB RAX RCX)
      And => emit (Alu AND RAX RCX)
      Or => emit (Alu OR RAX RCX)
      Xor => emit (Alu XOR RAX RCX)
      Mul => emit (Imul RAX RCX)
      Shl => emit (ShiftCl SHL RAX)
      Shr => emit (ShiftCl SHR RAX)
      Sar => emit (ShiftCl SAR RAX)
      DivS => emits [Cqo, Idiv RCX]
      RemS => emits [Cqo, Idiv RCX, MovRR RAX RDX]
      Operators.DivU => emits [Alu XOR RDX RDX, X86.DivU RCX]
      RemU => emits [Alu XOR RDX RDX, X86.DivU RCX, MovRR RAX RDX]
    maybe (pure ()) (\l => emit (Jcc O l)) ov

  ||| Turn twice a value, in the register, into the fixnum's word: `or` in
  ||| the fixnum tag, since the low bit is clear.
  addTag : {auto 0 fx : HasFixnums enc.val} -> Reg64 -> List X86.Instr
  addTag r = if fixnumTag enc.val == 0 then [] else [AluI OR r (cast (fixnumTag enc.val))]

  ||| Load twice a fixnum's value: its word less the fixnum tag, or an
  ||| immediate doubled.
  loadTwice : {auto 0 fx : HasFixnums enc.val} -> Reg64 -> Opnd enc -> Render enc ()
  loadTwice r (Imm c) = emit (MovRI r (2 * cast c))
  loadTwice r (StaticRef _) = failWith "a static where a fixnum is expected"
  loadTwice r (R x) = do
    loadReg r x
    when (fixnumTag enc.val /= 0) $ emit (AluI SUB r (cast (fixnumTag enc.val)))

  ||| Load a fixnum's value.
  loadValue : Reg64 -> Opnd enc -> Render enc ()
  loadValue r (Imm c) = emit (MovRI r (cast c))
  loadValue r (StaticRef _) = failWith "a static where a fixnum is expected"
  loadValue r (R x) = do loadReg r x; emit (ShiftI SAR r 1)

  ||| `op` of rax and twice the operand's value, an immediate folded into the
  ||| instruction where it fits.
  aluTwice : {auto 0 fx : HasFixnums enc.val} -> AluOp -> Opnd enc -> Render enc ()
  aluTwice op (Imm c) =
    let v = 2 * cast c in
    if fitsImm32 v then emit (AluI op RAX (cast v)) else emits [MovRI RCX v, Alu op RAX RCX]
  aluTwice op y = do loadTwice RCX y; emit (Alu op RAX RCX)

  ||| Arithmetic on fixnums, into rax, computed on their words. Where fixnum n
  ||| is the word w(n) = 2n + t, for the value encoding's fixnum tag t: x + y is
  ||| w(x) + 2y, x - y is w(x) - 2y and x xor y is w(x) xor 2y; x and y and
  ||| x or y are the words' own; x * y is 2x * y, then plus t. Each addition,
  ||| subtraction and multiplication overflows exactly when its result is
  ||| outside the fixnum range. A shift has no such identity: it takes the
  ||| values, shifts and tags.
  fixArith : {auto 0 fx : HasFixnums enc.val} -> ArithOp ->
             Opnd enc -> Opnd enc -> (overflow : Maybe X86.Label) -> Render enc ()
  fixArith o x y ov = case o of
      Add => do loadAs Fix RAX x; aluTwice ADD y; jo
      Sub => do loadAs Fix RAX x; aluTwice SUB y; jo
      Xor => do loadAs Fix RAX x; aluTwice XOR y
      And => do loadAs Fix RAX x; loadAs Fix RCX y; emit (Alu AND RAX RCX)
      Or => do loadAs Fix RAX x; loadAs Fix RCX y; emit (Alu OR RAX RCX)
      Mul => do loadTwice RAX x; loadValue RCX y; emit (Imul RAX RCX); jo; retag
      Shl => shift SHL
      Shr => shift SHR
      Sar => shift SAR
      _ => failWith ("the rendering does not support " ++ show o ++ " yet")
    where
      jo : Render enc ()
      jo = maybe (pure ()) (\l => emit (Jcc O l)) ov
      retag : Render enc ()
      retag = emits (addTag RAX)
      shift : ShiftOp -> Render enc ()
      shift sh = do
        loadValue RAX x
        loadValue RCX y
        emits [ShiftCl sh RAX, ShiftI SHL RAX 1]
        retag

  ------------------------------------------------------------------------------
  -- Saving what is live across a runtime call

  isOdd : Nat -> Bool
  isOdd Z = False
  isOdd (S Z) = True
  isOdd (S (S n)) = isOdd n

  ||| The live slots a call saves in ROOTS, and those it saves on the stack.
  ||| Across a call that can collect, the GC-visible ones go to ROOTS, where
  ||| the collector updates them; across one that cannot, every one goes to
  ||| the stack, since nothing moves.
  saved : (collects : Bool) -> List (Reg enc) -> (List (Reg enc), List (Reg enc))
  saved False live = ([], live)
  saved True live = (filter (gcVisible . regTy) live, filter (not . gcVisible . regTy) live)

  ||| Save the live slots across a call, as `saved` divides them, the ones on
  ||| the stack with a padding word when their number is odd so the call sees
  ||| a 16-aligned stack.
  saveLive : (collects : Bool) -> (X86.Instr -> Render enc ()) -> List (Reg enc) -> Render enc ()
  saveLive collects out live = do
    let (gc, raw) = saved collects live
    uses (MkAreas 0 (length gc) 0)
    when (not (null gc)) $ do
      out (Lea RSI (MRip (sym SymNRoots) 0))
      out (MovRM RDX (MBase RSI 0))
      out (MovRR RCX RDX)
      out (ShiftI SHL RCX 3)
      out (Lea RDI (MRip (sym SymRoots) 0))
      out (Alu ADD RDI RCX)
      traverse_ (\(j, r) => do n <- useSlot r
                               out (MovRM RCX (slotMem n))
                               out (MovMR (MBase RDI (cast (8 * j))) RCX))
                (zip (indices gc) gc)
      out (AluI ADD RDX (cast (length gc)))
      out (MovMR (MBase RSI 0) RDX)
    traverse_ (\r => do n <- useSlot r
                        out (MovRM RCX (slotMem n))
                        out (Push RCX)) raw
    when (isOdd (length raw)) $ out (Push RCX)
    where
      indices : List x -> List Nat
      indices xs = go 0 xs
        where go : Nat -> List x -> List Nat
              go _ [] = []
              go i (_ :: ys) = i :: go (S i) ys

  ||| Restore what `saveLive` saved, leaving rax alone.
  restoreLive : (collects : Bool) -> (X86.Instr -> Render enc ()) -> List (Reg enc) -> Render enc ()
  restoreLive collects out live = do
    let (gc, raw) = saved collects live
    traverse_ out setBase
    when (isOdd (length raw)) $ out (Pop RCX)
    traverse_ (\r => do n <- useSlot r
                        out (Pop RCX)
                        out (MovMR (slotMem n) RCX)) (reverse raw)
    when (not (null gc)) $ do
      out (Lea RSI (MRip (sym SymNRoots) 0))
      out (MovRM RDX (MBase RSI 0))
      out (AluI SUB RDX (cast (length gc)))
      out (MovMR (MBase RSI 0) RDX)
      out (ShiftI SHL RDX 3)
      out (Lea RDI (MRip (sym SymRoots) 0))
      out (Alu ADD RDI RDX)
      traverse_ (\(j, r) => do n <- useSlot r
                               out (MovRM RCX (MBase RDI (cast (8 * j))))
                               out (MovMR (slotMem n) RCX))
                (zip (indices gc) gc)
    where
      indices : List x -> List Nat
      indices xs = go 0 xs
        where go : Nat -> List x -> List Nat
              go _ [] = []
              go i (_ :: ys) = i :: go (S i) ys

  ||| Allocate `bytes` into rax: the fast path inline, the slow path cold, with
  ||| `live` saved across it. Leaves rax pointing at the uninitialised object.
  allocate : (bytes : Nat) -> (live : List (Reg enc)) -> Render enc ()
  allocate bytes live = do
    slow <- fresh
    done <- fresh
    emits [ MovRR RAX R15, Lea RCX (MBase R15 (cast bytes)), Alu CMP RCX R14, Jcc A slow
          , MovRR R15 RCX, Lbl done ]
    coldEmit (Lbl slow)
    saveLive True coldEmit live
    coldEmit (MovRI RDI (cast bytes))
    coldEmit (X86.Call (sym SymAllocSlow))
    coldEmit (MovRR RAX RDI)                   -- the routine's result, where a Direct result goes
    restoreLive True coldEmit live
    coldEmit (Jmp done)

  ||| The kinds whose objects are written after they are made. They are
  ||| allocated by a call to `idris_alloc_mutable`, never by the inline bump,
  ||| so that a collector with a nursery can keep them out of it, and then a
  ||| write into an old object never makes it point into the nursery.
  mutableKind : Kind -> Bool
  mutableKind IOREF = True
  mutableKind ARRAY = True
  mutableKind BUFFER = True
  mutableKind _ = False

  ||| Allocate a mutable object of the bytes `bytesInto` computes into a
  ||| register, by a call to `idris_alloc_mutable` with `live` saved across it.
  ||| Leaves rax pointing at the uninitialised object.
  allocateMutable : (bytesInto : Reg64 -> Render enc ()) -> (live : List (Reg enc)) -> Render enc ()
  allocateMutable bytesInto live = do
    saveLive True emit live
    bytesInto RDI
    emit (X86.Call (sym SymAllocMutable))
    emit (MovRR RAX RDI)
    restoreLive True emit live

  ||| Allocate an object whose size depends on `count`, as `allocate` does a
  ||| fixed one: `size r` turns the count in `r` into the object's bytes. The
  ||| slow path computes the size again from the count's slot, after saving
  ||| `live`, which holds the count. Leaves rax pointing at the uninitialised
  ||| object.
  allocateSized : (count : Reg enc) -> (size : Reg64 -> List X86.Instr) ->
                  (live : List (Reg enc)) -> Render enc ()
  allocateSized count size live = do
    slow <- fresh
    done <- fresh
    loadReg RDX count
    emits (size RDX)
    emits [ MovRR RAX R15, MovRR RCX R15, Alu ADD RCX RDX, Alu CMP RCX R14, Jcc A slow
          , MovRR R15 RCX, Lbl done ]
    coldEmit (Lbl slow)
    saveLive True coldEmit live
    n <- useSlot count
    coldEmit (MovRM RDI (slotMem n))
    traverse_ coldEmit (size RDI)
    coldEmit (X86.Call (sym SymAllocSlow))
    coldEmit (MovRR RAX RDI)
    restoreLive True coldEmit live
    coldEmit (Jmp done)

  ||| The base of a memory operand into `r`, plus its index scaled by `width`,
  ||| the access's width in bytes: an address that lives only within the
  ||| instruction that computes it.
  address : Reg64 -> LocatedIR.Mem enc -> (width : Nat) -> Render enc ()
  address r m width = do
    loadReg r m.base
    case m.index of
      Nothing => pure ()
      Just i => do loadReg RDX i
                   emits [ShiftI SHL RDX (shiftFor width), Alu ADD r RDX]
    where
      shiftFor : Nat -> Bits8
      shiftFor 1 = 0
      shiftFor 2 = 1
      shiftFor 4 = 2
      shiftFor _ = 3

  ||| The width of a sub-word access.
  width : SubWord -> Width
  width Sub8 = W8
  width Sub16 = W16
  width Sub32 = W32

  ------------------------------------------------------------------------------
  -- Instructions

  funLabel : Name -> Render enc X86.Label
  funLabel n = do
    s <- get
    case lookup n s.funs of
      Just l => pure l
      Nothing => failWith ("no function " ++ show n)

  ||| The label of a function outside the program: a routine of the runtime
  ||| contract that the runtime does not have yet, whose call ends the
  ||| program as `Unsupported` does.
  runtimeRoutine : Name -> Render enc X86.Label
  runtimeRoutine n =
    if any (\r => not r.provided && r.name == n) (routines {enc})
       then pure (sym SymUnsupported)
       else failWith ("no runtime routine " ++ show n)

  ||| Load an operand into a floating-point register: a slot's bits, or an
  ||| immediate's word, through rax.
  loadFloat : Xmm -> Opnd enc -> Render enc ()
  loadFloat x (R r) = do n <- useSlot r; emit (MovsdRM x (slotMem n))
  loadFloat x (Imm i) = emits [MovRI RAX (cast i), MovqXR x RAX]
  loadFloat x (StaticRef _) = failWith "a static where a double is expected"

  ||| Pass values of the types where `place` puts them, for a call or a
  ||| return: `ARGS` first, through rax and rcx, then the floating-point
  ||| registers, then the word registers, since rcx is one of them.
  putValues : List (Ty enc) -> List (Opnd enc) -> Render enc ()
  putValues tys xs = do
    uses (MkAreas (argsWords abi (map classOf tys)) 0 0)
    let items = zip3 (placeTys tys) tys xs
    traverse_ (\(l, t, x) => case l of
                               InArgs i => do emit (Lea RAX (MRip (sym SymArgs) 0))
                                              loadAs t RCX x
                                              emit (MovMR (MBase RAX (cast (8 * i))) RCX)
                               _ => pure ())
              items
    traverse_ (\(l, t, x) => case l of
                               InFloatReg f => loadFloat (xmm f) x
                               _ => pure ())
              items
    traverse_ (\(l, t, x) => case l of
                               InWordReg r => loadAs t (reg64 r) x
                               _ => pure ())
              items

  ||| Take values from where `place` puts them into the registers' slots: a
  ||| function's parameters on entry, or a direct call's results after it.
  ||| The registers first, then `ARGS`, through rax and rcx.
  takeValues : List (Reg enc) -> Render enc ()
  takeValues ds = do
    let tys = map regTy ds
        items = zip (placeTys tys) ds
    uses (MkAreas (argsWords abi (map classOf tys)) 0 0)
    traverse_ (\(l, d) => case l of
                            InWordReg r => store d (reg64 r)
                            InFloatReg f => do n <- useSlot d; emit (MovsdMR (slotMem n) (xmm f))
                            InArgs _ => pure ())
              items
    traverse_ (\(l, d) => case l of
                            InArgs i => do emit (Lea RAX (MRip (sym SymArgs) 0))
                                           emit (MovRM RCX (MBase RAX (cast (8 * i))))
                                           store d RCX
                            _ => pure ())
              items

  ||| A callee's parameter types, or, for a routine outside the program, the
  ||| arguments' own.
  paramTys : Name -> List (Opnd enc) -> Render enc (List (Ty enc))
  paramTys f args = do
    s <- get
    pure (fromMaybe (map opTy args) (lookup f s.params))

  instr : (LocatedIR.Label -> X86.Label) -> LocatedIR.Instr enc -> Render enc ()
  instr blk (Const d c) = do emit (MovRI RAX (immWord (regTy d) c)); store d RAX
  instr blk (CodeAddr d f) = do l <- funLabel f; emit (Lea RAX (MRip l 0)); store d RAX
  instr blk (StaticAddr d s) = do l <- staticLabel s; emit (Lea RAX (MRip l ptag)); store d RAX
  instr blk (Arith o d x y) = do
    case regTy d of
      Fix {fx} => fixArith o x y Nothing
      _ => wordArith o x y Nothing
    store d RAX
  instr blk (Unary o d x) = do
    loadReg RAX x
    emit (case o of Negate => Neg RAX; Complement => Not RAX)
    store d RAX
  instr blk (ArithOv o d x y l) = do
    case regTy d of
      Fix {fx} => fixArith o x y (Just (blk l))
      _ => wordArith o x y (Just (blk l))
    store d RAX
  instr blk (Cmp r d x y) = do
    emit (Alu XOR RDX RDX)
    loadAs (pairTy x y) RAX x
    compareWith (pairTy x y) y
    emit (Setcc (cond r) RDX)
    store d RDX
  instr blk (LocatedIR.Load _ d m) = do
    address RAX m 8
    emit (MovRM RCX (MBase RAX (m.offset - baseTag m.base)))
    store d RCX
  instr blk (LocatedIR.Store _ m x) = do
    address RAX m 8
    loadReg RCX x
    emit (MovMR (MBase RAX (m.offset - baseTag m.base)) RCX)
  instr blk (Tag {fx} d x) = do
    loadReg RAX x
    emits (ShiftI SHL RAX 1 :: addTag RAX)
    store d RAX
  instr blk (Untag d x) = do
    loadReg RAX x
    emit (ShiftI SAR RAX 1)
    store d RAX
  instr blk (TagOv {fx} d x l) = do
    loadReg RAX x
    emits ([Alu ADD RAX RAX, Jcc O (blk l)] ++ addTag RAX)
    store d RAX
  -- A narrowing reads the low part of the slot, which a little-endian word
  -- keeps first, extending it as it loads.
  instr blk (Ext sw s d x) = do
    n <- useSlot x
    emit (X86.Load (width sw) s RAX (slotMem n))
    store d RAX
  instr blk (Narrow _ d x) = do loadReg RAX x; store d RAX
  instr blk (Widen d x) = do loadReg RAX x; store d RAX
  instr blk (Move d x) = do loadReg RAX x; store d RAX
  -- a pointer word and an address are the same word
  instr blk (AddrToWord d x) = do loadReg RAX x; store d RAX
  instr blk (WordToAddr _ d x) = do loadReg RAX x; store d RAX
  instr blk (LoadPart p d o) = do
    loadReg RAX o
    emit (MovRM RAX (MBase RAX (negate (baseTag o))))
    emits (extractField RAX (cast (fst (HeapObject.place p))) (cast (snd (HeapObject.place p))))
    store d RAX
  instr blk (AllocObj {k} d h fs live) = do
    if mutableKind k
       then allocateMutable (\r => emit (MovRI r (cast (8 * objectWords h)))) live
       else allocate (8 * objectWords h) live
    emits [MovRI RDX (cast (encodeHeader h)), MovMR (MBase RAX 0) RDX]
    let (from, count) = scanned h
        fieldTy : Nat -> Ty enc
        fieldTy i = if S i >= from && S i < from + count then Val else W64
    traverse_ (\(i, f) => do loadAs (fieldTy i) RDX f
                             emit (MovMR (MBase RAX (cast (8 * (S i)))) RDX))
              (zip [0 .. length fs] fs)
    emits (tagPointer RAX RAX)
    store d RAX
  -- The count is checked against its part's bits first, so the size cannot
  -- wrap and the header holds the whole count. A mutable kind is allocated by
  -- a call, any other inline. The header is the kind's id plus the count in
  -- its part; a kind with scanned fields has each set to the fill, by a loop
  -- over the count.
  instr blk (AllocSized {k} d p count fill live) = do
    big <- fresh
    msg <- fresh
    let bytes = map (cast . ord) (unpack "object size out of range\n")
    modify { rodata $= (:< (msg, bytes)) }
    traverse_ coldEmit [ Lbl big, Lea RDI (MRip msg 0), MovRI RSI (cast (length bytes))
                       , Jmp (sym SymCrash) ]
    loadReg RCX count
    emits [MovRI RDX (cast (prim__shl_Integer 1 (cast (snd (HeapObject.place p))) - 1)), Alu CMP RCX RDX, Jcc A big]
    size <- sizeOf p
    if mutableKind k
       then allocateMutable (\r => do n <- useSlot count
                                      emit (MovRM r (slotMem n))
                                      emits (size r)) live
       else allocateSized count size live
    loadReg RDX count
    emits [ ShiftI SHL RDX (cast (fst (HeapObject.place p))), AluI ADD RDX (cast (kindId k))
          , MovMR (MBase RAX 0) RDX ]
    case fill of
      Nothing => pure ()
      Just f => do
        loop <- fresh
        end <- fresh
        loadReg RCX count
        loadAs Val RDX f
        emits [ Lea RDI (MBase RAX 8), Lbl loop, Test RCX RCX, Jcc E end
              , MovMR (MBase RDI 0) RDX, AluI ADD RDI 8, AluI SUB RCX 1, Jmp loop, Lbl end ]
    emits (tagPointer RAX RAX)
    store d RAX
    where
      -- The bytes of an object of `r` bytes of data: the header word, then the
      -- data rounded up to words.
      bytesSize : Reg64 -> List X86.Instr
      bytesSize r = [AluI ADD r 15, ShiftI SHR r 3, ShiftI SHL r 3]

      -- The object's bytes, from the count in `r`: the header word, then the
      -- elements as words, or the bytes rounded up to words.
      sizeOf : HeaderPart k' -> Render enc (Reg64 -> List X86.Instr)
      sizeOf ArrayElems = pure (\r => [ShiftI SHL r 3, AluI ADD r 8])
      -- a string made by its count is not known to be ASCII: its bit is 0,
      -- which only costs the fast paths
      sizeOf StringBytes = pure bytesSize
      sizeOf StringChars = pure (\r => ShiftI SHL r 2 :: bytesSize r)
      sizeOf BufferBytes = pure bytesSize
      sizeOf q = failWith ("AllocSized cannot size an object by " ++ show q)
  instr blk (DirectCall f args ds collects live) = do
    s <- get
    callee <- maybe (runtimeRoutine f) pure (lookup f s.funs)
    tys <- paramTys f args
    saveLive collects emit live
    putValues tys args
    emit (X86.Call callee)
    emits setBase
    takeValues ds
    restoreLive collects emit live
  instr blk (Convert I2F d x) = do
    loadReg RAX x
    emit (Cvtsi2sd XMM0 RAX)
    n <- useSlot d
    emit (MovsdMR (slotMem n) XMM0)
  instr blk (Convert F2I d x) = do
    n <- useSlot x
    emit (MovsdRM XMM0 (slotMem n))
    emit (Cvttsd2si RAX XMM0)
    store d RAX
  instr blk (Convert FBits d x) = do
    loadReg RAX x
    store d RAX
  instr blk (Convert BitsF d x) = do
    loadReg RAX x
    store d RAX
  -- A double's slot holds its bits, so a constant is a word and a negation
  -- flips the sign bit.
  instr blk (FConst d x) = do
    emit (MovRI RAX (doubleBits x))
    store d RAX
  instr blk (FNeg d x) = do
    loadReg RAX x
    emits [MovRI RCX 0x8000000000000000, Alu XOR RAX RCX]
    store d RAX
  instr blk (FArith o d x y) = do
    loadFloat XMM0 (R x)
    loadFloat XMM1 (R y)
    emit (Sse (case o of FAdd => ADDSD; FSub => SUBSD; FMul => MULSD; FDiv => DIVSD) XMM0 XMM1)
    n <- useSlot d
    emit (MovsdMR (slotMem n) XMM0)
  -- `ucomisd a, b` sets the flags as an unsigned comparison of a with b,
  -- and all of ZF, PF and CF when either is a NaN. So x < y is y above x and
  -- x <= y is y above or equal to x, which the NaN case fails; equality also
  -- needs PF clear, and inequality holds when PF is set.
  instr blk (FCmp r d x y) = do
    emits [Alu XOR RDX RDX, Alu XOR RCX RCX]
    loadFloat XMM0 (R x)
    loadFloat XMM1 (R y)
    emits $ case r of
      EqR => [Ucomisd XMM0 XMM1, Setcc E RDX, Setcc NP RCX, Alu AND RDX RCX]
      NeR => [Ucomisd XMM0 XMM1, Setcc NE RDX, Setcc P RCX, Alu OR RDX RCX]
      LtS => [Ucomisd XMM1 XMM0, Setcc A RDX]
      LtU => [Ucomisd XMM1 XMM0, Setcc A RDX]
      LeS => [Ucomisd XMM1 XMM0, Setcc AE RDX]
      LeU => [Ucomisd XMM1 XMM0, Setcc AE RDX]
      GtS => [Ucomisd XMM0 XMM1, Setcc A RDX]
      GtU => [Ucomisd XMM0 XMM1, Setcc A RDX]
      GeS => [Ucomisd XMM0 XMM1, Setcc AE RDX]
      GeU => [Ucomisd XMM0 XMM1, Setcc AE RDX]
    store d RDX
  instr blk (LoadN sw s d m) = do
    address RAX m (subWordBytes sw)
    emit (X86.Load (width sw) s RCX (MBase RAX (m.offset - baseTag m.base)))
    store d RCX
  instr blk (StoreN sw m x) = do
    address RAX m (subWordBytes sw)
    loadReg RCX x
    emit (X86.Store (width sw) (MBase RAX (m.offset - baseTag m.base)) RCX)
  -- The number in rax and the arguments where Linux takes them. The kernel
  -- keeps every register but rcx and r11, and the result is in rax.
  instr blk (AreaAddr d a) = do
    emit (Lea RAX (MRip (sym (areaSym a)) 0))
    store d RAX
  -- the pinned registers: the allocation window and the current continuation
  instr blk (LocatedIR.Intrinsic GetHp [d] []) = store d R15
  instr blk (LocatedIR.Intrinsic SetHp [] [x]) = load R15 x
  instr blk (LocatedIR.Intrinsic GetHpLim [d] []) = store d R14
  instr blk (LocatedIR.Intrinsic SetHpLim [] [x]) = load R14 x
  instr blk (LocatedIR.Intrinsic GetK [d] []) = store d R12
  instr blk (LocatedIR.Intrinsic SetK [] [x]) = load R12 x
  instr blk (LocatedIR.Intrinsic (IRCommon.Syscall _) [d] (n :: args)) =
    if length args > 6 then failWith "a system call of more than six arguments" else do
      traverse_ (\(r, x) => load r x) (zip [RDI, RSI, RDX, R10, R8, R9] args)
      load RAX n
      emits [X86.Syscall]
      store d RAX
  instr blk (LocatedIR.Loc _) = pure ()
  instr blk (LocatedIR.Comment s) = emit (X86.Comment s)
  instr blk i = failWith ("the rendering does not support " ++ instrName i ++ " yet")

  ------------------------------------------------------------------------------
  -- Terminators

  ||| Allocate and initialise the continuation of a non-tail call, and make it
  ||| the current one. Its layout word counts fewer than 2^24 GC-visible and
  ||| fewer than 2^24 raw values (`layoutWord`); a continuation keeping more
  ||| is refused.
  pushCont : (LocatedIR.Label -> X86.Label) -> Cont enc -> (alsoLive : List (Reg enc)) -> Render enc ()
  pushCont blk c alsoLive = do
    let vals = filter (gcVisible . regTy) c.live
        raws = filter (not . gcVisible . regTy) c.live
    when (length vals >= 16777216 || length raws >= 16777216) $
      failWith "a continuation keeps more values than its layout word counts"
    allocate (16 + 8 * length c.live) (c.live ++ alsoLive)
    emits [ Lea RDX (MRip (blk c.resume) 0), MovMR (MBase RAX 0) RDX
          , MovMR (MBase RAX 8) R12 ]
    traverse_ (\(i, r) => do n <- useSlot r
                             emit (MovRM RDX (slotMem n))
                             emit (MovMR (MBase RAX (cast (16 + 8 * i))) RDX))
              (zip [0 .. length c.live] (vals ++ raws))
    emits (tagPointer R12 RAX)

  argRegsOf : List (Opnd enc) -> List (Reg enc)
  argRegsOf = joinMap opRegs

  term : (LocatedIR.Label -> X86.Label) -> (results : List (Ty enc)) -> Terminator enc -> Render enc ()
  term blk res (Jump l) = emit (Jmp (blk l))
  -- Several tags in one test: under fixnum tag 1 every word is odd exactly
  -- when their `and` is, and under fixnum tag 0 every word is even exactly
  -- when their `or` is.
  term blk res (IfFixnums {fx} rs y n) = do
    case rs of
      [] => pure ()
      (r :: more) => do
        loadReg RAX r
        traverse_ (\x => do loadReg RCX x
                            emit (Alu (if fixnumTag enc.val == 0 then OR else AND) RAX RCX)) more
    emits [TestI RAX 1, Jcc (if fixnumTag enc.val == 0 then E else NE) (blk y), Jmp (blk n)]
  term blk res (Branch r x y t f) = do
    loadAs (pairTy x y) RAX x
    compareWith (pairTy x y) y
    emits [Jcc (cond r) (blk t), Jmp (blk f)]
  term blk res (Switch r cs d) = do
    loadReg RAX r
    traverse_ (\(v, l) => do compareWith (regTy r) (Imm v); emit (Jcc E (blk l))) cs
    emit (Jmp (blk d))
  term blk res (LocatedIR.Call f args c) = do
    l <- funLabel f
    pushCont blk c (argRegsOf args)
    putValues !(paramTys f args) args
    emit (Jmp l)
  term blk res (TailCall f args) = do
    l <- funLabel f
    putValues !(paramTys f args) args
    emit (Jmp l)
  term blk res (Apply f x c) = do
    pushCont blk c [f, x]
    loadReg RDI f
    loadReg RSI x
    emit (Jmp (sym SymApply))
  term blk res (TailApply f x) = do
    loadReg RDI f
    loadReg RSI x
    emit (Jmp (sym SymApply))
  term blk res (Return v) = do
    loadAs Val RAX v
    emit (JmpM (MBase R12 (negate ptag)))
  term blk res (Crash msg) = do
    l <- fresh
    let bytes = map (cast . ord) (unpack (msg ++ "\n"))
    modify { rodata $= (:< (l, bytes)) }
    emits [Lea RDI (MRip l 0), MovRI RSI (cast (length bytes)), Jmp (sym SymCrash)]
  term blk res (Unsupported _) = emit (Jmp (sym SymUnsupported))
  term blk res (LocatedIR.Ret xs) = do
    putValues res xs
    emits [AluI ADD RSP 8, X86.Ret]
  term blk res t = failWith ("the rendering does not support " ++ show (termName t) ++ " yet")

  ------------------------------------------------------------------------------
  -- Functions and the program

  ||| The live values a resume block reloads, in the order its continuation
  ||| stores them, and the layout word for them.
  resumes : Function enc -> SortedMap LocatedIR.Label (List (Reg enc), Integer)
  resumes f = fromList (mapMaybe resume f.blocks)
    where
      resume : Block enc -> Maybe (LocatedIR.Label, (List (Reg enc), Integer))
      resume b = do
        c <- termCont b.term
        let vals = filter (gcVisible . regTy) c.live
            raws = filter (not . gcVisible . regTy) c.live
        pure (c.resume, (vals ++ raws, layoutWord (cast (length vals)) (cast (length raws))))

  block : (LocatedIR.Label -> X86.Label) -> (results : List (Ty enc)) ->
          SortedMap LocatedIR.Label (List (Reg enc), Integer) -> Block enc -> Render enc ()
  block blk res rs b = do
    case lookup b.label rs of
      Just (live, word) => do
        emits (resumePoint (blk b.label) word)
        emits setBase
        case reverse b.params of
          (result :: _) => store result RAX
          [] => pure ()
        traverse_ (\(i, r) => do n <- useSlot r
                                 emit (MovRM RCX (MBase R12 (cast (16 + 8 * i) - ptag)))
                                 emit (MovMR (slotMem n) RCX))
                  (zip [0 .. length live] live)
        emit (MovRM R12 (MBase R12 (8 - ptag)))
      Nothing => emit (Lbl (blk b.label))
    traverse_ (instr blk) b.body
    term blk res b.term

  function : Function enc -> Render enc ()
  function f = do
    fl <- funLabel f.name
    labels <- traverse (\b => map (\l => (b.label, l)) fresh) f.blocks
    let table = fromList labels
        blk : LocatedIR.Label -> X86.Label
        blk n = fromMaybe 0 (lookup n table)
    emits [X86.Comment (show f.name), Lbl fl]
    -- a routine reached by symbol: the symbol is its entry too
    whenJust (routineSymbol {enc} f.name) $ \s => emit (Lbl (sym s))
    -- a machine call pushed a word: keep the stack 16-aligned inside; and
    -- below the stack limit, end the program
    case f.conv of
      Direct _ _ => emits [ AluI SUB RSP 8, MovRM RAX (MRip (sym SymStackLimit) 0), Alu CMP RSP RAX
                          , Jcc B (sym SymStackOverflow) ]
      CPS => pure ()
    emits setBase
    takeValues f.params
    emit (Jmp (blk f.entry))
    -- bound once: an argument of a partial application is evaluated again
    -- at every call of it, which read the function's blocks once per block
    let rs = resumes f
    traverse_ (block blk (results f.conv) rs) f.blocks
    s <- get
    put ({ text := s.text ++ s.cold, cold := [<] } s)

  staticBytes : Static enc -> Render enc (List Bits8)
  staticBytes s = do
    fields <- traverse field s.fields
    pure (contents (piece (le64 (cast (encodeHeader s.header))) <+> concatMap piece fields))
    where
      field : SField -> Render enc (List Bits8)
      field (SWord w) = pure (le64 (cast w))
      field _ = failWith ("the rendering does not support code or static references in statics yet")

  ||| The whole program: `main`, which the seed enters, jumps to the entry
  ||| function; every function follows; the statics and crash messages are
  ||| read-only data.
  export
  render : Program enc -> Either String Rendered
  render p = do
    let start = reservedLabels
        funs = fromList (zip (map (.name) p.functions) [start .. start + length p.functions])
        next1 = start + length p.functions
        statics = fromList (zip (map (.sym) p.statics) [next1 .. next1 + length p.statics])
        next2 = next1 + length p.statics
    let params = fromList (map (\f => (f.name, map regTy f.params)) p.functions)
        -- `idris_apply` stages a saturated closure's arguments in SCRATCH,
        -- and passes them as a call does, all `Val`s; a closure's arity is
        -- its function's number of parameters, and its function is CPS.
        arity = foldl max 0 [length f.params | f <- p.functions, f.conv == CPS]
        applyAreas = MkAreas (argsWords abi (replicate arity WordClass)) 0 arity
    (s, _) <- runStateT (MkRS next2 funs params statics [<] [<] [<] applyAreas) $ do
      entry <- funLabel p.entry
      emits [Lbl (sym SymMain), Jmp entry]
      traverse_ function p.functions
      traverse_ (\st => do l <- staticLabel st.sym
                           bytes <- staticBytes st
                           modify { rodata $= (:< (l, bytes)) })
                p.statics
    pure (MkRendered (s.text <>> []) (s.rodata <>> []) s.areas)
