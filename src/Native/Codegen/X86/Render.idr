||| The rendering of the IR as x86-64 instructions, under the heap lowering of
||| continuations.
|||
||| Registers. Every IR register is a `SCRATCH` slot (`Native.Codegen.LocatedIR.Reg`);
||| `rbx` holds `SCRATCH`'s address, so slot n is `[rbx + 8n]`, and is set at
||| every function entry, every resume point and after every runtime call,
||| since no register survives a transfer or a direct call. An instruction
||| loads its operands into `rax`, `rcx` and `rdx` and stores its result back.
||| `r15` and `r14` are the allocation window and `r12` the current
||| continuation, as `Native.Codegen.X86.Target.x86_64` pins them.
|||
||| Calls. Arguments travel where the target's `Abi` places them
||| (`Native.Codegen.Target.place`): words in rdi, rsi, rdx, rcx, r8 and r9,
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
||| (`Areas` in `Native.Codegen.Seed`), so no code writes past one.
|||
||| Invariants this rendering keeps: r12 holds a complete continuation at
||| every point where a collection can start and at every transfer; every
||| value live across a non-tail call is in the continuation it allocated,
||| and every value live across a tail call is an argument; and a
||| continuation is fully initialised before r12 is set to it, so no
||| collection can see a partial one.
module Native.Codegen.X86.Render

import Native.Codegen.X86.Asm
import Native.Codegen.X86.Target

import Control.Monad.State.Interface
import Control.Monad.State.State
import Control.Monad.Trans
import Core.Name
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.Zippable
import Native.Area
import Native.Codegen.Bytes
import Native.Codegen.IRCommon.Conv as IRCommon
import Native.Codegen.IRCommon.Intrinsic
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Codegen.Linkage.Areas as Linkage
import Native.Codegen.Linkage.Realised as Linkage
import Native.Codegen.Linkage.ResumePoint
import Native.Codegen.Linkage.Routine as Linkage
import Native.Codegen.Linkage.Sym as Linkage
import Native.Codegen.LocatedIR.Block as LocatedIR
import Native.Codegen.LocatedIR.Cont as LocatedIR
import Native.Codegen.LocatedIR.Function as LocatedIR
import Native.Codegen.LocatedIR.Instr as LocatedIR
import Native.Codegen.LocatedIR.Label as LocatedIR
import Native.Codegen.LocatedIR.Mem as LocatedIR
import Native.Codegen.LocatedIR.Opnd as LocatedIR
import Native.Codegen.LocatedIR.Program as LocatedIR
import Native.Codegen.LocatedIR.Reg as LocatedIR
import Native.Codegen.LocatedIR.Static as LocatedIR
import Native.Codegen.LocatedIR.Terminator as LocatedIR
import Native.Codegen.Target
import Native.Data.Builder as Data
import Native.HeapObj.Enc as HeapObj
import Native.HeapObj.Header as HeapObj
import Native.HeapObj.Kind as HeapObj
import Native.HeapObj.LayoutWord
import Native.HeapObj.ValEnc

%default covering

||| What the rendering gives the linker: the program's code, which defines the
||| seed's `main` label, its read-only data, and the per-thread areas its code
||| uses.
public export
record Rendered where
  constructor MkRendered
  text : List Asm.Instr
  rodata : List (Asm.Label, List Bits8)
  areas : Linkage.Areas

record RS (enc : HeapObj.Enc) where
  constructor MkRS
  nextLabel : Nat
  funs : SortedMap Name Asm.Label
  ||| Each function's parameter types: an immediate argument for a `Val` or a
  ||| `Fix` parameter is an integer, whose word the value encoding gives.
  params : SortedMap Name (List (IRCommon.Ty enc))
  statics : SortedMap Name Asm.Label
  ||| The code so far, accumulating at its end.
  text : SnocList Asm.Instr
  ||| Slow paths, placed after the function being rendered.
  cold : SnocList Asm.Instr
  rodata : SnocList (Asm.Label, List Bits8)
  ||| The most of each per-thread area the code so far uses.
  areas : Linkage.Areas

-- Everything below renders for the program's encodings, and the contract as
-- the loaded runtime realises it. The value encoding decides how a `Val`
-- immediate and a fixnum are words, and the pointer tag every access
-- through a pointer folds into its displacement.

parameters (enc : HeapObj.Enc) (realised : Linkage.Realised)
  ------------------------------------------------------------------------------
  -- Operands

  ------------------------------------------------------------------------------
  -- Arithmetic

  ------------------------------------------------------------------------------
  -- Saving what is live across a runtime call

  ------------------------------------------------------------------------------
  -- Instructions

  ------------------------------------------------------------------------------
  -- Terminators

  ------------------------------------------------------------------------------
  -- Functions and the program

  ||| The whole program: `main`, which the seed enters, jumps to the entry
  ||| function; every function follows; the statics and crash messages are
  ||| read-only data.
  export
  render : LocatedIR.Program enc -> Either String Rendered
  render p = do
    let start = Linkage.Sym.reservedLabels
        funs = fromList (zip (map (.name) p.functions) [start .. start + length p.functions])
        next1 = start + length p.functions
        statics = fromList (zip (map (.sym) p.statics) [next1 .. next1 + length p.statics])
        next2 = next1 + length p.statics
    let params = fromList (map (\f => (f.name, map LocatedIR.Reg.regTy f.params)) p.functions)
        -- `idris_apply` stages a saturated closure's arguments in SCRATCH,
        -- and passes them as a call does, all `Val`s; a closure's arity is
        -- its function's number of parameters, and its function is CPS.
        arity = foldl max 0 [length f.params | f <- p.functions, f.conv == IRCommon.Conv.CPS]
        applyAreas = Linkage.MkAreas (Target.argsWords abi (replicate arity Target.WordClass)) 0 arity
    (s, _) <- runStateT (MkRS next2 funs params statics [<] [<] [<] applyAreas) $ do
      entry <- funLabel p.entry
      emits [Asm.Lbl (sym Linkage.Sym.SymMain), Asm.Jmp entry]
      traverse_ function p.functions
      traverse_ (\st => do l <- staticLabel st.sym
                           bytes <- staticBytes st
                           modify { rodata $= (:< (l, bytes)) })
                p.statics
    pure (MkRendered (s.text <>> []) (s.rodata <>> []) s.areas)
    where
      Render : HeapObj.Enc -> Type -> Type
      Render enc = StateT (RS enc) (Either String)

      failWith : String -> Render enc' a
      failWith = lift . Left

      staticBytes : LocatedIR.Static enc -> Render enc (List Bits8)
      staticBytes s = do
        fields <- traverse field s.fields
        pure
          (toList
            (Data.Builder.piece (Bytes.le64 (cast (HeapObj.Header.encodeHeader s.header)))
             <+> concatMap Data.Builder.piece fields))
        where
          field : LocatedIR.Static.SField -> Render enc (List Bits8)
          field (LocatedIR.Static.SWord w) = pure (Bytes.le64 (cast w))
          field _ = failWith ("the rendering does not support code or static references in statics yet")

      emit : Asm.Instr -> Render enc' ()
      emit i = modify { text $= (:< i) }

      emits : List Asm.Instr -> Render enc' ()
      emits = traverse_ emit

      sym : Linkage.Sym -> Asm.Label
      sym = Linkage.Sym.symLabel

      abi : Target.Abi
      abi = Target.x86_64.abi

      staticLabel : Name -> Render enc Asm.Label
      staticLabel n = do
        s <- get
        case lookup n s.statics of
          Just l => pure l
          Nothing => failWith ("no static " ++ show n)

      funLabel : Name -> Render enc Asm.Label
      funLabel n = do
        s <- get
        case lookup n s.funs of
          Just l => pure l
          Nothing => failWith ("no function " ++ show n)

      function : LocatedIR.Function enc -> Render enc ()
      function f = do
        fl <- funLabel f.name
        labels <- traverse (\b => map (\l => (b.label, l)) fresh) f.blocks
        let table = fromList labels
            blk : LocatedIR.Label -> Asm.Label
            blk n = fromMaybe 0 (lookup n table)
        emits [Asm.Comment (show f.name), Asm.Lbl fl]
        -- a routine reached by symbol: the symbol is its entry too
        whenJust (Linkage.Routine.routineSymbol {enc} realised f.name) $ \s => emit (Asm.Lbl (sym s))
        -- a machine call pushed a word: keep the stack 16-aligned inside; and
        -- below the stack limit, end the program
        case f.conv of
          IRCommon.Conv.Direct _ _ =>
            emits [ Asm.AluI Asm.SUB Asm.RSP 8,
                   Asm.MovRM Asm.RAX (Asm.MRip (sym Linkage.Sym.SymStackLimit) 0), Asm.Alu Asm.CMP Asm.RSP Asm.RAX
                                            , Asm.Jcc Asm.B (sym Linkage.Sym.SymStackOverflow) ]
          IRCommon.Conv.CPS => pure ()
        emits setBase
        takeValues f.params
        emit (Asm.Jmp (blk f.entry))
        -- bound once: an argument of a partial application is evaluated again
        -- at every call of it, which read the function's blocks once per block
        let rs = resumes f
        traverse_ (block blk (results f.conv) rs) f.blocks
        s <- get
        put ({ text := s.text ++ s.cold, cold := [<] } s)
        where
          ||| The live values a resume block reloads, in the order its continuation
          ||| stores them, and the layout word for them.
          resumes : LocatedIR.Function enc -> SortedMap LocatedIR.Label (List (LocatedIR.Reg enc), Integer)
          resumes f = fromList (mapMaybe resume f.blocks)
            where
              resume : LocatedIR.Block enc -> Maybe (LocatedIR.Label, (List (LocatedIR.Reg enc), Integer))
              resume b = do
                c <- LocatedIR.Terminator.termCont b.term
                let vals = filter (IRCommon.Ty.gcVisible . LocatedIR.Reg.regTy) c.live
                    raws = filter (not . IRCommon.Ty.gcVisible . LocatedIR.Reg.regTy) c.live
                pure (c.resume, (vals ++ raws, HeapObj.LayoutWord.layoutWord (cast (length vals)) (cast (length raws))))

          ||| Record that the code uses at least these areas.
          uses : Linkage.Areas -> Render enc' ()
          uses a = modify { areas $= Linkage.Areas.maxAreas a }

          ||| The register's slot, recorded as used.
          useSlot : LocatedIR.Reg enc -> Render enc Nat
          useSlot r = do let n = LocatedIR.Reg.slotOf r
                         uses (Linkage.MkAreas 0 0 (S n))
                         pure n

          slotMem : Nat -> Asm.Mem
          slotMem n = Asm.MBase Asm.RBX (cast (8 * n))

          store : LocatedIR.Reg enc -> Asm.Reg64 -> Render enc ()
          store d r = do n <- useSlot d; emit (Asm.MovMR (slotMem n) r)

          reg64 : Target.TargetReg -> Asm.Reg64
          reg64 = Asm.regOfNum

          xmm : Target.FloatReg -> Asm.Xmm
          xmm = Asm.xmmOfNum

          ||| Where values of the types travel between functions.
          placeTys : List (IRCommon.Ty enc) -> List Target.Loc
          placeTys tys = Target.place abi (map IRCommon.Ty.classOf tys)

          ||| Take values from where `place` puts them into the registers' slots: a
          ||| function's parameters on entry, or a direct call's results after it.
          ||| The registers first, then `ARGS`, through rax and rcx.
          takeValues : List (LocatedIR.Reg enc) -> Render enc ()
          takeValues ds = do
            let tys = map LocatedIR.Reg.regTy ds
                items = zip (placeTys tys) ds
            uses (Linkage.MkAreas (Target.argsWords abi (map IRCommon.Ty.classOf tys)) 0 0)
            traverse_ (\(l, d) => case l of
                                    Target.InWordReg r => store d (reg64 r)
                                    Target.InFloatReg f => do n <- useSlot d; emit (Asm.MovsdMR (slotMem n) (xmm f))
                                    Target.InArgs _ => pure ())
                      items
            traverse_ (\(l, d) => case l of
                                    Target.InArgs i => do emit (Asm.Lea Asm.RAX (Asm.MRip (sym Linkage.Sym.SymArgs) 0))
                                                          emit (Asm.MovRM Asm.RCX (Asm.MBase Asm.RAX (cast (8 * i))))
                                                          store d Asm.RCX
                                    _ => pure ())
                      items

          ||| The pointer tag of the value encoding: a pointer word is the object's address
          ||| plus it, so every load and store through a pointer folds its negation
          ||| into the displacement.
          ptag : Int
          ptag = cast (HeapObj.ValEnc.pointerTag enc.val)

          ||| Turn the object address in `s` into its pointer word in `d`.
          tagPointer : (d, s : Asm.Reg64) -> List Asm.Instr
          tagPointer d s = if ptag == 0 then (if d == s then [] else [Asm.MovRR d s])
            else [Asm.Lea d (Asm.MBase s ptag)]

          ||| The type two compared operands share: the register's, if either is one.
          pairTy : LocatedIR.Opnd enc -> LocatedIR.Opnd enc -> IRCommon.Ty enc
          pairTy (LocatedIR.Opnd.R x) _ = LocatedIR.Reg.regTy x
          pairTy _ (LocatedIR.Opnd.R y) = LocatedIR.Reg.regTy y
          pairTy (LocatedIR.Opnd.StaticRef _) _ = IRCommon.Ty.Val
          pairTy _ (LocatedIR.Opnd.StaticRef _) = IRCommon.Ty.Val
          pairTy _ _ = IRCommon.Ty.W64

          cond : IRCommon.Op.Rel -> Asm.Cond
          cond IRCommon.Op.EqR = Asm.E
          cond IRCommon.Op.NeR = Asm.NE
          cond IRCommon.Op.LtS = Asm.L
          cond IRCommon.Op.LeS = Asm.LE
          cond IRCommon.Op.GtS = Asm.G
          cond IRCommon.Op.GeS = Asm.GE
          cond IRCommon.Op.LtU = Asm.B
          cond IRCommon.Op.LeU = Asm.BE
          cond IRCommon.Op.GtU = Asm.A
          cond IRCommon.Op.GeU = Asm.AE

          ||| The word of an immediate where a value of the type is expected: in a
          ||| `Val` or `Fix` position the immediate is an integer, and the value
          ||| encoding gives its word; elsewhere it is the word itself. The term's
          ||| immediates carry the proof that the value encoding has a word for them.
          immWord : IRCommon.Ty enc -> Int64 -> Integer
          immWord IRCommon.Ty.Val i = maybe (cast i) cast (HeapObj.ValEnc.valWord enc.val (cast i))
          immWord IRCommon.Ty.Fix i = maybe (cast i) cast (HeapObj.ValEnc.valWord enc.val (cast i))
          immWord _ i = cast i

          ||| Load an operand where a value of the type is expected.
          loadAs : IRCommon.Ty enc -> Asm.Reg64 -> LocatedIR.Opnd enc -> Render enc ()
          loadAs t r (LocatedIR.Opnd.Imm i) = emit (Asm.MovRI r (immWord t i))
          loadAs _ r (LocatedIR.Opnd.StaticRef s) = do l <- staticLabel s; emit (Asm.Lea r (Asm.MRip l ptag))
          loadAs _ r (LocatedIR.Opnd.R x) = do n <- useSlot x; emit (Asm.MovRM r (slotMem n))

          ||| Load a raw operand.
          load : Asm.Reg64 -> LocatedIR.Opnd enc -> Render enc ()
          load = loadAs IRCommon.Ty.W64

          loadReg : Asm.Reg64 -> LocatedIR.Reg enc -> Render enc ()
          loadReg r x = load r (LocatedIR.Opnd.R x)

          fitsImm32 : Integer -> Bool
          fitsImm32 i = i >= -2147483648 && i <= 2147483647

          ||| Compare rax with the operand, where a value of the type is expected:
          ||| `test` against the word 0, an immediate compare where the word fits.
          compareWith : IRCommon.Ty enc -> LocatedIR.Opnd enc -> Render enc ()
          compareWith t (LocatedIR.Opnd.Imm c) =
            let w = immWord t c in
            if w == 0 then emit (Asm.Test Asm.RAX Asm.RAX)
            else if fitsImm32 w then emit (Asm.AluI Asm.CMP Asm.RAX (cast w))
            else emits [Asm.MovRI Asm.RCX w, Asm.Alu Asm.CMP Asm.RAX Asm.RCX]
          compareWith _ (LocatedIR.Opnd.R y) = do loadReg Asm.RCX y; emit (Asm.Alu Asm.CMP Asm.RAX Asm.RCX)
          compareWith _ (LocatedIR.Opnd.StaticRef s) = do l <- staticLabel s
                                                          emits [Asm.Lea Asm.RCX (Asm.MRip l ptag),
                                                                 Asm.Alu Asm.CMP Asm.RAX Asm.RCX]

          coldEmit : Asm.Instr -> Render enc' ()
          coldEmit i = modify { cold $= (:< i) }

          fresh : Render enc' Asm.Label
          fresh = do
            s <- get
            put ({ nextLabel := S s.nextLabel } s)
            pure s.nextLabel

          isOdd : Nat -> Bool
          isOdd Z = False
          isOdd (S Z) = True
          isOdd (S (S n)) = isOdd n

          ||| The live slots a call saves in ROOTS, and those it saves on the stack.
          ||| Across a call that can collect, the GC-visible ones go to ROOTS, where
          ||| the collector updates them; across one that cannot, every one goes to
          ||| the stack, since nothing moves.
          saved : (collects : Bool) -> List (LocatedIR.Reg enc) -> (List (LocatedIR.Reg enc), List (LocatedIR.Reg enc))
          saved False live = ([], live)
          saved True live =
            (filter (IRCommon.Ty.gcVisible . LocatedIR.Reg.regTy) live,
             filter (not . IRCommon.Ty.gcVisible . LocatedIR.Reg.regTy) live)

          ||| Save the live slots across a call, as `saved` divides them, the ones on
          ||| the stack with a padding word when their number is odd so the call sees
          ||| a 16-aligned stack.
          saveLive : (collects : Bool) -> (Asm.Instr -> Render enc ()) -> List (LocatedIR.Reg enc) -> Render enc ()
          saveLive collects out live = do
            let (gc, raw) = saved collects live
            uses (Linkage.MkAreas 0 (length gc) 0)
            when (not (null gc)) $ do
              out (Asm.Lea Asm.RSI (Asm.MRip (sym Linkage.Sym.SymNRoots) 0))
              out (Asm.MovRM Asm.RDX (Asm.MBase Asm.RSI 0))
              out (Asm.MovRR Asm.RCX Asm.RDX)
              out (Asm.ShiftI Asm.SHL Asm.RCX (cast Area.rootShift))
              out (Asm.Lea Asm.RDI (Asm.MRip (sym Linkage.Sym.SymRoots) 0))
              out (Asm.Alu Asm.ADD Asm.RDI Asm.RCX)
              traverse_ (\(j, r) => do n <- useSlot r
                                       out (Asm.MovRM Asm.RCX (slotMem n))
                                       out (Asm.MovMR (Asm.MBase Asm.RDI (cast (Area.rootOffset (cast j)))) Asm.RCX))
                        (zip (indices gc) gc)
              out (Asm.AluI Asm.ADD Asm.RDX (cast (length gc)))
              out (Asm.MovMR (Asm.MBase Asm.RSI 0) Asm.RDX)
            traverse_ (\r => do n <- useSlot r
                                out (Asm.MovRM Asm.RCX (slotMem n))
                                out (Asm.Push Asm.RCX)) raw
            when (isOdd (length raw)) $ out (Asm.Push Asm.RCX)
            where
              indices : List x -> List Nat
              indices xs = go 0 xs
                where go : Nat -> List x -> List Nat
                      go _ [] = []
                      go i (_ :: ys) = i :: go (S i) ys

          setBase : List Asm.Instr
          setBase = [Asm.Lea Asm.RBX (Asm.MRip (sym Linkage.Sym.SymScratch) 0)]

          ||| Restore what `saveLive` saved, leaving rax alone.
          restoreLive : (collects : Bool) -> (Asm.Instr -> Render enc ()) -> List (LocatedIR.Reg enc) -> Render enc ()
          restoreLive collects out live = do
            let (gc, raw) = saved collects live
            traverse_ out setBase
            when (isOdd (length raw)) $ out (Asm.Pop Asm.RCX)
            traverse_ (\r => do n <- useSlot r
                                out (Asm.Pop Asm.RCX)
                                out (Asm.MovMR (slotMem n) Asm.RCX)) (reverse raw)
            when (not (null gc)) $ do
              out (Asm.Lea Asm.RSI (Asm.MRip (sym Linkage.Sym.SymNRoots) 0))
              out (Asm.MovRM Asm.RDX (Asm.MBase Asm.RSI 0))
              out (Asm.AluI Asm.SUB Asm.RDX (cast (length gc)))
              out (Asm.MovMR (Asm.MBase Asm.RSI 0) Asm.RDX)
              out (Asm.ShiftI Asm.SHL Asm.RDX (cast Area.rootShift))
              out (Asm.Lea Asm.RDI (Asm.MRip (sym Linkage.Sym.SymRoots) 0))
              out (Asm.Alu Asm.ADD Asm.RDI Asm.RDX)
              traverse_ (\(j, r) => do n <- useSlot r
                                       out (Asm.MovRM Asm.RCX (Asm.MBase Asm.RDI (cast (Area.rootOffset (cast j)))))
                                       out (Asm.MovMR (slotMem n) Asm.RCX))
                        (zip (indices gc) gc)
            where
              indices : List x -> List Nat
              indices xs = go 0 xs
                where go : Nat -> List x -> List Nat
                      go _ [] = []
                      go i (_ :: ys) = i :: go (S i) ys

          ||| Allocate `bytes` into rax: the fast path inline, the slow path cold, with
          ||| `live` saved across it. Leaves rax pointing at the uninitialised object.
          allocate : (bytes : Nat) -> (live : List (LocatedIR.Reg enc)) -> Render enc ()
          allocate bytes live = do
            slow <- fresh
            done <- fresh
            emits [ Asm.MovRR Asm.RAX Asm.R15,
                   Asm.Lea Asm.RCX (Asm.MBase Asm.R15 (cast bytes)), Asm.Alu Asm.CMP Asm.RCX Asm.R14, Asm.Jcc Asm.A slow
                  , Asm.MovRR Asm.R15 Asm.RCX, Asm.Lbl done ]
            coldEmit (Asm.Lbl slow)
            saveLive True coldEmit live
            coldEmit (Asm.MovRI Asm.RDI (cast bytes))
            coldEmit (Asm.Call (sym Linkage.Sym.SymAllocSlow))
            coldEmit (Asm.MovRR Asm.RAX Asm.RDI)                   -- the routine's result, where a Direct result goes
            restoreLive True coldEmit live
            coldEmit (Asm.Jmp done)

          ||| Load an operand into a floating-point register: a slot's bits, or an
          ||| immediate's word, through rax.
          loadFloat : Asm.Xmm -> LocatedIR.Opnd enc -> Render enc ()
          loadFloat x (LocatedIR.Opnd.R r) = do n <- useSlot r; emit (Asm.MovsdRM x (slotMem n))
          loadFloat x (LocatedIR.Opnd.Imm i) = emits [Asm.MovRI Asm.RAX (cast i), Asm.MovqXR x Asm.RAX]
          loadFloat x (LocatedIR.Opnd.StaticRef _) = failWith "a static where a double is expected"

          ||| Pass values of the types where `place` puts them, for a call or a
          ||| return: `ARGS` first, through rax and rcx, then the floating-point
          ||| registers, then the word registers, since rcx is one of them.
          putValues : List (IRCommon.Ty enc) -> List (LocatedIR.Opnd enc) -> Render enc ()
          putValues tys xs = do
            uses (Linkage.MkAreas (Target.argsWords abi (map IRCommon.Ty.classOf tys)) 0 0)
            let items = zip3 (placeTys tys) tys xs
            traverse_ (\(l, t, x) => case l of
                                       Target.InArgs i => do emit
                                                               (Asm.Lea Asm.RAX (Asm.MRip (sym Linkage.Sym.SymArgs) 0))
                                                             loadAs t Asm.RCX x
                                                             emit (Asm.MovMR (Asm.MBase Asm.RAX (cast (8 * i))) Asm.RCX)
                                       _ => pure ())
                      items
            traverse_ (\(l, t, x) => case l of
                                       Target.InFloatReg f => loadFloat (xmm f) x
                                       _ => pure ())
                      items
            traverse_ (\(l, t, x) => case l of
                                       Target.InWordReg r => loadAs t (reg64 r) x
                                       _ => pure ())
                      items

          ||| A callee's parameter types, or, for a routine outside the program, the
          ||| arguments' own.
          paramTys : Name -> List (LocatedIR.Opnd enc) -> Render enc (List (IRCommon.Ty enc))
          paramTys f args = do
            s <- get
            pure (fromMaybe (map opTy args) (lookup f s.params))
            where
              ||| The type of an operand: its register's, or a word for an immediate.
              opTy : LocatedIR.Opnd enc -> IRCommon.Ty enc
              opTy (LocatedIR.Opnd.R r) = LocatedIR.Reg.regTy r
              opTy (LocatedIR.Opnd.Imm _) = IRCommon.Ty.W64
              opTy (LocatedIR.Opnd.StaticRef _) = IRCommon.Ty.Val

          term : (LocatedIR.Label -> Asm.Label) -> (results : List (IRCommon.Ty enc)) -> LocatedIR.Terminator enc ->
                 Render enc ()
          term blk res terminator = case terminator of
            LocatedIR.Terminator.Jump l => emit (Asm.Jmp (blk l))
            -- Several tags in one test: under fixnum tag 1 every word is odd exactly
            -- when their `and` is, and under fixnum tag 0 every word is even exactly
            -- when their `or` is.
            LocatedIR.Terminator.IfFixnums {fx} rs y n => do
                                   case rs of
                                     [] => pure ()
                                     (r :: more) => do
                                       loadReg Asm.RAX r
                                       traverse_ (\x => do loadReg Asm.RCX x
                                                           emit
                                                             (Asm.Alu
                                                               (if HeapObj.ValEnc.fixnumTag enc.val == 0 then Asm.OR
                                                                else Asm.AND)
                                                              Asm.RAX Asm.RCX))
                                                               more
                                   emits [Asm.TestI Asm.RAX 1,
                                     Asm.Jcc (if HeapObj.ValEnc.fixnumTag enc.val == 0 then Asm.E else Asm.NE) (blk y),
                                          Asm.Jmp (blk n)]
            LocatedIR.Terminator.Branch r x y t f => do
                                   loadAs (pairTy x y) Asm.RAX x
                                   compareWith (pairTy x y) y
                                   emits [Asm.Jcc (cond r) (blk t), Asm.Jmp (blk f)]
            LocatedIR.Terminator.Switch r cs d => do
                                   loadReg Asm.RAX r
                                   traverse_ (\(v, l) => do compareWith (LocatedIR.Reg.regTy r) (LocatedIR.Opnd.Imm v)
                                                            emit (Asm.Jcc Asm.E (blk l))) cs
                                   emit (Asm.Jmp (blk d))
            LocatedIR.Terminator.Call f args c => do
              l <- funLabel f
              pushCont blk c (argRegsOf args)
              putValues !(paramTys f args) args
              emit (Asm.Jmp l)
            LocatedIR.Terminator.TailCall f args => do
                                   l <- funLabel f
                                   putValues !(paramTys f args) args
                                   emit (Asm.Jmp l)
            LocatedIR.Terminator.Apply f x c => do
                                   pushCont blk c [f, x]
                                   loadReg Asm.RDI f
                                   loadReg Asm.RSI x
                                   emit (Asm.Jmp (sym Linkage.Sym.SymApply))
            LocatedIR.Terminator.TailApply f x => do
                                   loadReg Asm.RDI f
                                   loadReg Asm.RSI x
                                   emit (Asm.Jmp (sym Linkage.Sym.SymApply))
            LocatedIR.Terminator.Return v => do
                                   loadAs IRCommon.Ty.Val Asm.RAX v
                                   emit (Asm.JmpM (Asm.MBase Asm.R12 (negate ptag)))
            LocatedIR.Terminator.Crash msg => do
                                   l <- fresh
                                   let bytes = map (cast . ord) (unpack (msg ++ "\n"))
                                   modify { rodata $= (:< (l, bytes)) }
                                   emits [Asm.Lea Asm.RDI (Asm.MRip l 0),
                                          Asm.MovRI Asm.RSI (cast (length bytes)), Asm.Jmp (sym Linkage.Sym.SymCrash)]
            LocatedIR.Terminator.Unsupported _ => emit (Asm.Jmp (sym Linkage.Sym.SymUnsupported))
            LocatedIR.Terminator.Ret xs => do
              putValues res xs
              emits [Asm.AluI Asm.ADD Asm.RSP 8, Asm.Ret]
            t => failWith ("the rendering does not support " ++ show (LocatedIR.Terminator.termName t) ++ " yet")
            where
              argRegsOf : List (LocatedIR.Opnd enc) -> List (LocatedIR.Reg enc)
              argRegsOf = Data.Builder.joinMap LocatedIR.Opnd.opRegs

              ||| Allocate and initialise the continuation of a non-tail call, and make it
              ||| the current one. Its layout word counts fewer than 2^24 GC-visible and
              ||| fewer than 2^24 raw values (`layoutWord`); a continuation keeping more
              ||| is refused.
              pushCont : (LocatedIR.Label -> Asm.Label) -> LocatedIR.Cont enc ->
                         (alsoLive : List (LocatedIR.Reg enc)) -> Render enc ()
              pushCont blk c alsoLive = do
                let vals = filter (IRCommon.Ty.gcVisible . LocatedIR.Reg.regTy) c.live
                    raws = filter (not . IRCommon.Ty.gcVisible . LocatedIR.Reg.regTy) c.live
                when (length vals >= 16777216 || length raws >= 16777216) $
                  failWith "a continuation keeps more values than its layout word counts"
                allocate (16 + 8 * length c.live) (c.live ++ alsoLive)
                emits [ Asm.Lea Asm.RDX (Asm.MRip (blk c.resume) 0), Asm.MovMR (Asm.MBase Asm.RAX 0) Asm.RDX
                      , Asm.MovMR (Asm.MBase Asm.RAX 8) Asm.R12 ]
                traverse_ (\(i, r) => do n <- useSlot r
                                         emit (Asm.MovRM Asm.RDX (slotMem n))
                                         emit (Asm.MovMR (Asm.MBase Asm.RAX (cast (16 + 8 * i))) Asm.RDX))
                          (zip [0 .. length c.live] (vals ++ raws))
                emits (tagPointer Asm.R12 Asm.RAX)

          block : (LocatedIR.Label -> Asm.Label) -> (results : List (IRCommon.Ty enc)) ->
                  SortedMap LocatedIR.Label (List (LocatedIR.Reg enc), Integer) -> LocatedIR.Block enc -> Render enc ()
          block blk res rs b = do
            case lookup b.label rs of
              Just (live, word) => do
                emits (Linkage.ResumePoint.resumePoint (blk b.label) word)
                emits setBase
                case reverse b.params of
                  (result :: _) => store result Asm.RAX
                  [] => pure ()
                traverse_ (\(i, r) => do n <- useSlot r
                                         emit (Asm.MovRM Asm.RCX (Asm.MBase Asm.R12 (cast (16 + 8 * i) - ptag)))
                                         emit (Asm.MovMR (slotMem n) Asm.RCX))
                          (zip [0 .. length live] live)
                emit (Asm.MovRM Asm.R12 (Asm.MBase Asm.R12 (8 - ptag)))
              Nothing => emit (Asm.Lbl (blk b.label))
            traverse_ (instr blk) b.body
            term blk res b.term
            where
              instr : (LocatedIR.Label -> Asm.Label) -> LocatedIR.Instr enc -> Render enc ()
              instr blk instr' = case instr' of
                LocatedIR.Instr.Const d c => do emit (Asm.MovRI Asm.RAX (immWord (LocatedIR.Reg.regTy d) c))
                                                store d Asm.RAX
                LocatedIR.Instr.CodeAddr d f => do l <- funLabel f
                                                   emit (Asm.Lea Asm.RAX (Asm.MRip l 0))
                                                   store d Asm.RAX
                LocatedIR.Instr.StaticAddr d s => do l <- staticLabel s
                                                     emit (Asm.Lea Asm.RAX (Asm.MRip l ptag))
                                                     store d Asm.RAX
                LocatedIR.Instr.Arith o d x y => do
                                  case LocatedIR.Reg.regTy d of
                                    IRCommon.Ty.Fix {fx} => fixArith o x y Nothing
                                    _ => wordArith o x y Nothing
                                  store d Asm.RAX
                LocatedIR.Instr.Unary o d x => do
                                  loadReg Asm.RAX x
                                  emit (case o of IRCommon.Op.Negate => Asm.Neg Asm.RAX
                                                  IRCommon.Op.Complement => Asm.Not Asm.RAX)
                                  store d Asm.RAX
                LocatedIR.Instr.ArithOv o d x y l => do
                                  case LocatedIR.Reg.regTy d of
                                    IRCommon.Ty.Fix {fx} => fixArith o x y (Just (blk l))
                                    _ => wordArith o x y (Just (blk l))
                                  store d Asm.RAX
                LocatedIR.Instr.Cmp r d x y => do
                                  emit (Asm.Alu Asm.XOR Asm.RDX Asm.RDX)
                                  loadAs (pairTy x y) Asm.RAX x
                                  compareWith (pairTy x y) y
                                  emit (Asm.Setcc (cond r) Asm.RDX)
                                  store d Asm.RDX
                LocatedIR.Instr.Load _ d m => do
                  address Asm.RAX m 8
                  emit (Asm.MovRM Asm.RCX (Asm.MBase Asm.RAX (m.offset - baseTag m.base)))
                  store d Asm.RCX
                LocatedIR.Instr.Store _ m x => do
                  address Asm.RAX m 8
                  loadReg Asm.RCX x
                  emit (Asm.MovMR (Asm.MBase Asm.RAX (m.offset - baseTag m.base)) Asm.RCX)
                LocatedIR.Instr.Tag {fx} d x => do
                                  loadReg Asm.RAX x
                                  emits (Asm.ShiftI Asm.SHL Asm.RAX 1 :: addTag Asm.RAX)
                                  store d Asm.RAX
                LocatedIR.Instr.Untag d x => do
                                  loadReg Asm.RAX x
                                  emit (Asm.ShiftI Asm.SAR Asm.RAX 1)
                                  store d Asm.RAX
                LocatedIR.Instr.TagOv {fx} d x l => do
                                  loadReg Asm.RAX x
                                  emits ([Asm.Alu Asm.ADD Asm.RAX Asm.RAX, Asm.Jcc Asm.O (blk l)] ++ addTag Asm.RAX)
                                  store d Asm.RAX
                -- A narrowing reads the low part of the slot, which a little-endian word
                -- keeps first, extending it as it loads.
                LocatedIR.Instr.Ext sw s d x => do
                                  n <- useSlot x
                                  emit (Asm.Load (width sw) s Asm.RAX (slotMem n))
                                  store d Asm.RAX
                LocatedIR.Instr.Narrow _ d x => do loadReg Asm.RAX x; store d Asm.RAX
                LocatedIR.Instr.Widen d x => do loadReg Asm.RAX x; store d Asm.RAX
                LocatedIR.Instr.Move d x => do loadReg Asm.RAX x; store d Asm.RAX
                -- a pointer word and an address are the same word
                LocatedIR.Instr.AddrToWord d x => do loadReg Asm.RAX x; store d Asm.RAX
                LocatedIR.Instr.WordToAddr _ d x => do loadReg Asm.RAX x; store d Asm.RAX
                LocatedIR.Instr.ValToWord d x => do loadReg Asm.RAX x; store d Asm.RAX
                LocatedIR.Instr.WordToVal d x => do loadReg Asm.RAX x; store d Asm.RAX
                LocatedIR.Instr.LoadPart p d o => do
                                  loadReg Asm.RAX o
                                  emit (Asm.MovRM Asm.RAX (Asm.MBase Asm.RAX (negate (baseTag o))))
                                  emits
                                    (Asm.extractField Asm.RAX (cast (fst (HeapObj.Header.place p)))
                                     (cast (snd (HeapObj.Header.place p))))
                                  store d Asm.RAX
                LocatedIR.Instr.AllocObj {k} d h fs live => do
                                  if mutableKind k
                                     then allocateMutable
                                       (\r => emit (Asm.MovRI r (cast (8 * HeapObj.Header.objectWords h)))) live
                                     else allocate (8 * HeapObj.Header.objectWords h) live
                                  emits [Asm.MovRI Asm.RDX (cast (HeapObj.Header.encodeHeader h)),
                                         Asm.MovMR (Asm.MBase Asm.RAX 0) Asm.RDX]
                                  let (from, count) = HeapObj.Header.scanned h
                                      fieldTy : Nat -> IRCommon.Ty enc
                                      fieldTy i = if S i >= from && S i < from + count then IRCommon.Ty.Val
                                        else IRCommon.Ty.W64
                                  traverse_ (\(i, f) => do loadAs (fieldTy i) Asm.RDX f
                                                           emit
                                                             (Asm.MovMR (Asm.MBase Asm.RAX (cast (8 * (S i)))) Asm.RDX))
                                            (zip [0 .. length fs] fs)
                                  emits (tagPointer Asm.RAX Asm.RAX)
                                  store d Asm.RAX
                -- The count is checked against its part's bits first, so the size cannot
                -- wrap and the header holds the whole count. A mutable kind is allocated by
                -- a call, any other inline. The header is the kind's fixed word plus the count in
                -- its part; a kind with scanned fields has each set to the fill, by a loop
                -- over the count.
                LocatedIR.Instr.AllocSized {k} d p count fill live => do
                                  big <- fresh
                                  msg <- fresh
                                  let bytes = map (cast . ord) (unpack "object size out of range\n")
                                  modify { rodata $= (:< (msg, bytes)) }
                                  traverse_ coldEmit
                                    [ Asm.Lbl big, Asm.Lea Asm.RDI (Asm.MRip msg 0),
                                     Asm.MovRI Asm.RSI (cast (length bytes))
                                                     , Asm.Jmp (sym Linkage.Sym.SymCrash) ]
                                  loadReg Asm.RCX count
                                  emits
                                    [Asm.MovRI Asm.RDX
                                      (cast (prim__shl_Integer 1 (cast (snd (HeapObj.Header.place p))) - 1)),
                                     Asm.Alu Asm.CMP Asm.RCX Asm.RDX, Asm.Jcc Asm.A big]
                                  size <- sizeOf p
                                  if mutableKind k
                                     then allocateMutable (\r => do n <- useSlot count
                                                                    emit (Asm.MovRM r (slotMem n))
                                                                    emits (size r)) live
                                     else allocateSized count size live
                                  loadReg Asm.RDX count
                                  emits [ Asm.ShiftI Asm.SHL Asm.RDX (cast (fst (HeapObj.Header.place p))),
                                         Asm.AluI Asm.ADD Asm.RDX (cast (HeapObj.Header.fixedWord k))
                                        , Asm.MovMR (Asm.MBase Asm.RAX 0) Asm.RDX ]
                                  case fill of
                                    Nothing => pure ()
                                    Just f => do
                                      loop <- fresh
                                      end <- fresh
                                      loadReg Asm.RCX count
                                      loadAs IRCommon.Ty.Val Asm.RDX f
                                      emits [ Asm.Lea Asm.RDI (Asm.MBase Asm.RAX 8),
                                             Asm.Lbl loop, Asm.Test Asm.RCX Asm.RCX, Asm.Jcc Asm.E end
                                            , Asm.MovMR (Asm.MBase Asm.RDI 0) Asm.RDX, Asm.AluI Asm.ADD Asm.RDI 8,
                                              Asm.AluI Asm.SUB Asm.RCX 1, Asm.Jmp loop, Asm.Lbl end ]
                                  emits (tagPointer Asm.RAX Asm.RAX)
                                  store d Asm.RAX
                LocatedIR.Instr.DirectCall f args ds collects live => do
                                  s <- get
                                  callee <- maybe (runtimeRoutine f) pure (lookup f s.funs)
                                  tys <- paramTys f args
                                  saveLive collects emit live
                                  putValues tys args
                                  emit (Asm.Call callee)
                                  emits setBase
                                  takeValues ds
                                  restoreLive collects emit live
                LocatedIR.Instr.Convert IRCommon.Op.I2F d x => do
                                  loadReg Asm.RAX x
                                  emit (Asm.Cvtsi2sd Asm.XMM0 Asm.RAX)
                                  n <- useSlot d
                                  emit (Asm.MovsdMR (slotMem n) Asm.XMM0)
                LocatedIR.Instr.Convert IRCommon.Op.F2I d x => do
                                  n <- useSlot x
                                  emit (Asm.MovsdRM Asm.XMM0 (slotMem n))
                                  emit (Asm.Cvttsd2si Asm.RAX Asm.XMM0)
                                  store d Asm.RAX
                LocatedIR.Instr.Convert IRCommon.Op.FBits d x => do
                                  loadReg Asm.RAX x
                                  store d Asm.RAX
                LocatedIR.Instr.Convert IRCommon.Op.BitsF d x => do
                                  loadReg Asm.RAX x
                                  store d Asm.RAX
                -- A double's slot holds its bits, so a constant is a word and a negation
                -- flips the sign bit.
                LocatedIR.Instr.FConst d x => do
                                  emit (Asm.MovRI Asm.RAX (Bytes.doubleBits x))
                                  store d Asm.RAX
                LocatedIR.Instr.FNeg d x => do
                                  loadReg Asm.RAX x
                                  emits [Asm.MovRI Asm.RCX 0x8000000000000000, Asm.Alu Asm.XOR Asm.RAX Asm.RCX]
                                  store d Asm.RAX
                LocatedIR.Instr.FArith o d x y => do
                                  loadFloat Asm.XMM0 (LocatedIR.Opnd.R x)
                                  loadFloat Asm.XMM1 (LocatedIR.Opnd.R y)
                                  emit
                                    (Asm.Sse (case o of IRCommon.Op.FAdd => Asm.ADDSD
                                                        IRCommon.Op.FSub => Asm.SUBSD
                                                        IRCommon.Op.FMul => Asm.MULSD
                                                        IRCommon.Op.FDiv => Asm.DIVSD) Asm.XMM0 Asm.XMM1)
                                  n <- useSlot d
                                  emit (Asm.MovsdMR (slotMem n) Asm.XMM0)
                -- `ucomisd a, b` sets the flags as an unsigned comparison of a with b,
                -- and all of ZF, PF and CF when either is a NaN. So x < y is y above x and
                -- x <= y is y above or equal to x, which the NaN case fails; equality also
                -- needs PF clear, and inequality holds when PF is set.
                LocatedIR.Instr.FCmp r d x y => do
                                  emits [Asm.Alu Asm.XOR Asm.RDX Asm.RDX, Asm.Alu Asm.XOR Asm.RCX Asm.RCX]
                                  loadFloat Asm.XMM0 (LocatedIR.Opnd.R x)
                                  loadFloat Asm.XMM1 (LocatedIR.Opnd.R y)
                                  emits $ case r of
                                    IRCommon.Op.EqR =>
                                      [Asm.Ucomisd Asm.XMM0 Asm.XMM1, Asm.Setcc Asm.E Asm.RDX, Asm.Setcc Asm.NP Asm.RCX,
                                       Asm.Alu Asm.AND Asm.RDX Asm.RCX]
                                    IRCommon.Op.NeR =>
                                      [Asm.Ucomisd Asm.XMM0 Asm.XMM1, Asm.Setcc Asm.NE Asm.RDX, Asm.Setcc Asm.P Asm.RCX,
                                       Asm.Alu Asm.OR Asm.RDX Asm.RCX]
                                    IRCommon.Op.LtS => [Asm.Ucomisd Asm.XMM1 Asm.XMM0, Asm.Setcc Asm.A Asm.RDX]
                                    IRCommon.Op.LtU => [Asm.Ucomisd Asm.XMM1 Asm.XMM0, Asm.Setcc Asm.A Asm.RDX]
                                    IRCommon.Op.LeS => [Asm.Ucomisd Asm.XMM1 Asm.XMM0, Asm.Setcc Asm.AE Asm.RDX]
                                    IRCommon.Op.LeU => [Asm.Ucomisd Asm.XMM1 Asm.XMM0, Asm.Setcc Asm.AE Asm.RDX]
                                    IRCommon.Op.GtS => [Asm.Ucomisd Asm.XMM0 Asm.XMM1, Asm.Setcc Asm.A Asm.RDX]
                                    IRCommon.Op.GtU => [Asm.Ucomisd Asm.XMM0 Asm.XMM1, Asm.Setcc Asm.A Asm.RDX]
                                    IRCommon.Op.GeS => [Asm.Ucomisd Asm.XMM0 Asm.XMM1, Asm.Setcc Asm.AE Asm.RDX]
                                    IRCommon.Op.GeU => [Asm.Ucomisd Asm.XMM0 Asm.XMM1, Asm.Setcc Asm.AE Asm.RDX]
                                  store d Asm.RDX
                LocatedIR.Instr.LoadN sw s d m => do
                                  address Asm.RAX m (IRCommon.Op.subWordBytes sw)
                                  emit (Asm.Load (width sw) s Asm.RCX (Asm.MBase Asm.RAX (m.offset - baseTag m.base)))
                                  store d Asm.RCX
                LocatedIR.Instr.StoreN sw m x => do
                                  address Asm.RAX m (IRCommon.Op.subWordBytes sw)
                                  loadReg Asm.RCX x
                                  emit (Asm.Store (width sw) (Asm.MBase Asm.RAX (m.offset - baseTag m.base)) Asm.RCX)
                -- The number in rax and the arguments where Linux takes them. The kernel
                -- keeps every register but rcx and r11, and the result is in rax.
                LocatedIR.Instr.AreaAddr d a => do
                                  emit (Asm.Lea Asm.RAX (Asm.MRip (sym (Linkage.Sym.areaSym a)) 0))
                                  store d Asm.RAX
                -- the pinned registers: the allocation window and the current continuation
                LocatedIR.Instr.Intrinsic IRCommon.Intrinsic.GetHp [d] [] => store d Asm.R15
                LocatedIR.Instr.Intrinsic IRCommon.Intrinsic.SetHp [] [x] => load Asm.R15 x
                LocatedIR.Instr.Intrinsic IRCommon.Intrinsic.GetHpLim [d] [] => store d Asm.R14
                LocatedIR.Instr.Intrinsic IRCommon.Intrinsic.SetHpLim [] [x] => load Asm.R14 x
                LocatedIR.Instr.Intrinsic IRCommon.Intrinsic.GetK [d] [] => store d Asm.R12
                LocatedIR.Instr.Intrinsic IRCommon.Intrinsic.SetK [] [x] => load Asm.R12 x
                LocatedIR.Instr.Intrinsic (IRCommon.Intrinsic.Syscall _) [d] (n :: args) =>
                  if length args > 6 then failWith "a system call of more than six arguments" else do
                    traverse_ (\(r, x) => load r x) (zip [Asm.RDI, Asm.RSI, Asm.RDX, Asm.R10, Asm.R8, Asm.R9] args)
                    load Asm.RAX n
                    emits [Asm.Syscall]
                    store d Asm.RAX
                LocatedIR.Instr.Loc _ => pure ()
                LocatedIR.Instr.Comment s => emit (Asm.Comment s)
                i => failWith ("the rendering does not support " ++ LocatedIR.Instr.instrName i ++ " yet")
                where
                  -- The bytes of an object of `r` bytes of data: the header word, then the
                  -- data rounded up to words.
                  bytesSize : Asm.Reg64 -> List Asm.Instr
                  bytesSize r = [Asm.AluI Asm.ADD r 15, Asm.ShiftI Asm.SHR r 3, Asm.ShiftI Asm.SHL r 3]

                  -- The object's bytes, from the count in `r`: the header word, then the
                  -- elements as words, or the bytes rounded up to words.
                  sizeOf : HeapObj.Header.HeaderPart k' -> Render enc (Asm.Reg64 -> List Asm.Instr)
                  sizeOf HeapObj.Header.ArrayElems = pure (\r => [Asm.ShiftI Asm.SHL r 3, Asm.AluI Asm.ADD r 8])
                  -- a string made by its count is not known to be ASCII: its bit is 0,
                  -- which only costs the fast paths
                  sizeOf HeapObj.Header.StringBytes = pure bytesSize
                  sizeOf HeapObj.Header.StringChars = pure (\r => Asm.ShiftI Asm.SHL r 2 :: bytesSize r)
                  sizeOf HeapObj.Header.BufferBytes = pure bytesSize
                  sizeOf q = failWith ("AllocSized cannot size an object by " ++ show q)

                  ||| Allocate an object whose size depends on `count`, as `allocate` does a
                  ||| fixed one: `size r` turns the count in `r` into the object's bytes. The
                  ||| slow path computes the size again from the count's slot, after saving
                  ||| `live`, which holds the count. Leaves rax pointing at the uninitialised
                  ||| object.
                  allocateSized : (count : LocatedIR.Reg enc) -> (size : Asm.Reg64 -> List Asm.Instr) ->
                                  (live : List (LocatedIR.Reg enc)) -> Render enc ()
                  allocateSized count size live = do
                    slow <- fresh
                    done <- fresh
                    loadReg Asm.RDX count
                    emits (size Asm.RDX)
                    emits [ Asm.MovRR Asm.RAX Asm.R15,
                      Asm.MovRR Asm.RCX Asm.R15, Asm.Alu Asm.ADD Asm.RCX Asm.RDX, Asm.Alu Asm.CMP Asm.RCX Asm.R14,
                           Asm.Jcc Asm.A slow
                          , Asm.MovRR Asm.R15 Asm.RCX, Asm.Lbl done ]
                    coldEmit (Asm.Lbl slow)
                    saveLive True coldEmit live
                    n <- useSlot count
                    coldEmit (Asm.MovRM Asm.RDI (slotMem n))
                    traverse_ coldEmit (size Asm.RDI)
                    coldEmit (Asm.Call (sym Linkage.Sym.SymAllocSlow))
                    coldEmit (Asm.MovRR Asm.RAX Asm.RDI)
                    restoreLive True coldEmit live
                    coldEmit (Asm.Jmp done)

                  ||| The label of a function outside the program: a routine of the runtime
                  ||| contract that the runtime does not have yet, whose call ends the
                  ||| program as `Unsupported` does.
                  runtimeRoutine : Name -> Render enc Asm.Label
                  runtimeRoutine n =
                    if any (\r => not r.provided && r.name == n) (Linkage.Routine.routines {enc} realised)
                       then pure (sym Linkage.Sym.SymUnsupported)
                       else failWith ("no runtime routine " ++ show n)

                  ||| What a load or store through the register subtracts: the pointer tag if
                  ||| the register holds a pointer word, nothing if it holds an address.
                  baseTag : LocatedIR.Reg enc -> Int
                  baseTag r = if IRCommon.Ty.gcVisible (LocatedIR.Reg.regTy r) then ptag else 0

                  ||| Arithmetic on raw words, into rax.
                  wordArith : IRCommon.Op.ArithOp -> LocatedIR.Opnd enc -> LocatedIR.Opnd enc ->
                              (overflow : Maybe Asm.Label) -> Render enc ()
                  wordArith o x y ov = do
                    load Asm.RAX x
                    load Asm.RCX y
                    case o of
                      IRCommon.Op.Add => emit (Asm.Alu Asm.ADD Asm.RAX Asm.RCX)
                      IRCommon.Op.Sub => emit (Asm.Alu Asm.SUB Asm.RAX Asm.RCX)
                      IRCommon.Op.And => emit (Asm.Alu Asm.AND Asm.RAX Asm.RCX)
                      IRCommon.Op.Or => emit (Asm.Alu Asm.OR Asm.RAX Asm.RCX)
                      IRCommon.Op.Xor => emit (Asm.Alu Asm.XOR Asm.RAX Asm.RCX)
                      IRCommon.Op.Mul => emit (Asm.Imul Asm.RAX Asm.RCX)
                      IRCommon.Op.Shl => emit (Asm.ShiftCl Asm.SHL Asm.RAX)
                      IRCommon.Op.Shr => emit (Asm.ShiftCl Asm.SHR Asm.RAX)
                      IRCommon.Op.Sar => emit (Asm.ShiftCl Asm.SAR Asm.RAX)
                      IRCommon.Op.DivS => emits [Asm.Cqo, Asm.Idiv Asm.RCX]
                      IRCommon.Op.RemS => emits [Asm.Cqo, Asm.Idiv Asm.RCX, Asm.MovRR Asm.RAX Asm.RDX]
                      IRCommon.Op.DivU => emits [Asm.Alu Asm.XOR Asm.RDX Asm.RDX, Asm.DivU Asm.RCX]
                      IRCommon.Op.RemU =>
                        emits [Asm.Alu Asm.XOR Asm.RDX Asm.RDX, Asm.DivU Asm.RCX, Asm.MovRR Asm.RAX Asm.RDX]
                    maybe (pure ()) (\l => emit (Asm.Jcc Asm.O l)) ov

                  ||| Turn twice a value, in the register, into the fixnum's word: `or` in
                  ||| the fixnum tag, since the low bit is clear.
                  addTag : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} -> Asm.Reg64 -> List Asm.Instr
                  addTag r = if HeapObj.ValEnc.fixnumTag enc.val == 0 then []
                    else [Asm.AluI Asm.OR r (cast (HeapObj.ValEnc.fixnumTag enc.val))]

                  ||| Arithmetic on fixnums, into rax, computed on their words. Where fixnum n
                  ||| is the word w(n) = 2n + t, for the value encoding's fixnum tag t: x + y is
                  ||| w(x) + 2y, x - y is w(x) - 2y and x xor y is w(x) xor 2y; x and y and
                  ||| x or y are the words' own; x * y is 2x * y, then plus t. Each addition,
                  ||| subtraction and multiplication overflows exactly when its result is
                  ||| outside the fixnum range. A shift has no such identity: it takes the
                  ||| values, shifts and tags.
                  fixArith : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} -> IRCommon.Op.ArithOp ->
                             LocatedIR.Opnd enc -> LocatedIR.Opnd enc -> (overflow : Maybe Asm.Label) -> Render enc ()
                  fixArith o x y ov = case o of
                      IRCommon.Op.Add => do loadAs IRCommon.Ty.Fix Asm.RAX x; aluTwice Asm.ADD y; jo
                      IRCommon.Op.Sub => do loadAs IRCommon.Ty.Fix Asm.RAX x; aluTwice Asm.SUB y; jo
                      IRCommon.Op.Xor => do loadAs IRCommon.Ty.Fix Asm.RAX x; aluTwice Asm.XOR y
                      IRCommon.Op.And => do loadAs IRCommon.Ty.Fix Asm.RAX x
                                            loadAs IRCommon.Ty.Fix Asm.RCX y
                                            emit (Asm.Alu Asm.AND Asm.RAX Asm.RCX)
                      IRCommon.Op.Or => do loadAs IRCommon.Ty.Fix Asm.RAX x
                                           loadAs IRCommon.Ty.Fix Asm.RCX y
                                           emit (Asm.Alu Asm.OR Asm.RAX Asm.RCX)
                      IRCommon.Op.Mul => do loadTwice Asm.RAX x
                                            loadValue Asm.RCX y
                                            emit (Asm.Imul Asm.RAX Asm.RCX)
                                            jo
                                            retag
                      IRCommon.Op.Shl => shift Asm.SHL
                      IRCommon.Op.Shr => shift Asm.SHR
                      IRCommon.Op.Sar => shift Asm.SAR
                      _ => failWith ("the rendering does not support " ++ show o ++ " yet")
                    where
                      jo : Render enc ()
                      jo = maybe (pure ()) (\l => emit (Asm.Jcc Asm.O l)) ov
                      retag : Render enc ()
                      retag = emits (addTag Asm.RAX)
                      ||| Load a fixnum's value.
                      loadValue : Asm.Reg64 -> LocatedIR.Opnd enc -> Render enc ()
                      loadValue r (LocatedIR.Opnd.Imm c) = emit (Asm.MovRI r (cast c))
                      loadValue r (LocatedIR.Opnd.StaticRef _) = failWith "a static where a fixnum is expected"
                      loadValue r (LocatedIR.Opnd.R x) = do loadReg r x; emit (Asm.ShiftI Asm.SAR r 1)

                      shift : Asm.ShiftOp -> Render enc ()
                      shift sh = do
                        loadValue Asm.RAX x
                        loadValue Asm.RCX y
                        emits [Asm.ShiftCl sh Asm.RAX, Asm.ShiftI Asm.SHL Asm.RAX 1]
                        retag

                      ||| Load twice a fixnum's value: its word less the fixnum tag, or an
                      ||| immediate doubled.
                      loadTwice : Asm.Reg64 -> LocatedIR.Opnd enc -> Render enc ()
                      loadTwice r (LocatedIR.Opnd.Imm c) = emit (Asm.MovRI r (2 * cast c))
                      loadTwice r (LocatedIR.Opnd.StaticRef _) = failWith "a static where a fixnum is expected"
                      loadTwice r (LocatedIR.Opnd.R x) = do
                        loadReg r x
                        when (HeapObj.ValEnc.fixnumTag enc.val /= 0) $
                          emit (Asm.AluI Asm.SUB r (cast (HeapObj.ValEnc.fixnumTag enc.val)))

                      ||| `op` of rax and twice the operand's value, an immediate folded into the
                      ||| instruction where it fits.
                      aluTwice : Asm.AluOp -> LocatedIR.Opnd enc -> Render enc ()
                      aluTwice op (LocatedIR.Opnd.Imm c) =
                        let v = 2 * cast c in
                        if fitsImm32 v then emit (Asm.AluI op Asm.RAX (cast v))
                          else emits [Asm.MovRI Asm.RCX v, Asm.Alu op Asm.RAX Asm.RCX]
                      aluTwice op y = do loadTwice Asm.RCX y; emit (Asm.Alu op Asm.RAX Asm.RCX)

                  ||| The kinds whose objects are written after they are made. They are
                  ||| allocated by a call to `idris_alloc_mutable`, never by the inline bump,
                  ||| so that a collector with a nursery can keep them out of it, and then a
                  ||| write into an old object never makes it point into the nursery.
                  mutableKind : HeapObj.Kind -> Bool
                  mutableKind HeapObj.Kind.IOREF = True
                  mutableKind HeapObj.Kind.ARRAY = True
                  mutableKind HeapObj.Kind.BUFFER = True
                  mutableKind _ = False

                  ||| Allocate a mutable object of the bytes `bytesInto` computes into a
                  ||| register, by a call to `idris_alloc_mutable` with `live` saved across it.
                  ||| Leaves rax pointing at the uninitialised object.
                  allocateMutable : (bytesInto : Asm.Reg64 -> Render enc ()) -> (live : List (LocatedIR.Reg enc)) ->
                                    Render enc ()
                  allocateMutable bytesInto live = do
                    saveLive True emit live
                    bytesInto Asm.RDI
                    emit (Asm.Call (sym Linkage.Sym.SymAllocMutable))
                    emit (Asm.MovRR Asm.RAX Asm.RDI)
                    restoreLive True emit live

                  ||| The base of a memory operand into `r`, plus its index scaled by `width`,
                  ||| the access's width in bytes: an address that lives only within the
                  ||| instruction that computes it.
                  address : Asm.Reg64 -> LocatedIR.Mem enc -> (width : Nat) -> Render enc ()
                  address r m width = do
                    loadReg r m.base
                    case m.index of
                      Nothing => pure ()
                      Just i => do loadReg Asm.RDX i
                                   emits [Asm.ShiftI Asm.SHL Asm.RDX (shiftFor width), Asm.Alu Asm.ADD r Asm.RDX]
                    where
                      shiftFor : Nat -> Bits8
                      shiftFor 1 = 0
                      shiftFor 2 = 1
                      shiftFor 4 = 2
                      shiftFor _ = 3

                  ||| The width of a sub-word access.
                  width : IRCommon.Op.SubWord -> Asm.Width
                  width IRCommon.Op.Sub8 = Asm.W8
                  width IRCommon.Op.Sub16 = Asm.W16
                  width IRCommon.Op.Sub32 = Asm.W32
