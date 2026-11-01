||| The rendering of the IR as x86-64 instructions, under the heap lowering of
||| continuations.
|||
||| Locations. Every value of the IR is in a location
||| (`Native.Codegen.LocatedIR.Location`): a slot, CPS code's in `SCRATCH`,
||| since a CPS function never nests, a Direct function's in its own frame
||| on the machine stack, or one of the target's allocatable registers.
||| `rbx` holds the slots' base, so slot n is `[rbx + 8n]`, and is set at
||| every function entry, every resume point and after every runtime call,
||| since no register survives a transfer or a direct call. An instruction
||| finds its operands in the registers its row (`Native.Codegen.X86.Rows`)
||| wants them in, where register allocation moved them, or reads them where
||| they are, and writes its results where they go. Every allocatable
||| register its code writes is a result's or one its row names, checked as
||| it is rendered (`conforming`), so that register allocation, which reads
||| the rows, keeps no value in a register the code destroys.
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
||| Direct functions. A Direct function lowers the stack on entry by its
||| frame, its registers' slots, an odd number of words, so that the stack
||| stays 16-aligned inside it since the call pushed one, and raises it again
||| before it returns. On entry it also compares the stack pointer with the
||| limit the seed sets at start-up (`STACK_LIMIT`), and below it ends the
||| program with a message, so that deep recursion in direct code is
||| reported rather than a fault. A direct call passes the arguments as a
||| call does and executes a machine call; the callee's `Ret` passes its
||| results where `place` puts arguments, and the caller stores them in its
||| result registers' slots, `ARGS` first emptied. No callee writes its
||| caller's slots, so a direct call saves nothing, but one that can collect
||| puts the GC-visible values live across it in `ROOTS`, where the
||| collector forwards them, and reloads them from there (`saveLive`).
|||
||| Allocation. An object or a continuation is a bump of r15, then a check of
||| it against r14. Past the limit, the site's cold code, placed after the
||| function, calls the slow path every site shares, with the site's live
||| table after the call (`Native.Codegen.X86.AllocLive`): it saves what is
||| live across `idris_alloc_slow` (the GC-visible values in `ROOTS`, where
||| the collector forwards them, the raw ones in its own frame), restores
||| it, and returns to the jump back to the initialisation.
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

import Native.Codegen.X86.AccessWidth
import Native.Codegen.X86.AllocLive
import Native.Codegen.X86.Asm
import Native.Codegen.X86.Datum
import Native.Codegen.X86.RegSet
import Native.Codegen.X86.Rows
import Native.Codegen.X86.Writes

import Core.Name
import Data.Bits
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.Zippable
import Native.Area
import Native.Codegen.IRCommon.Conv as IRCommon
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Pinned as IRCommon
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Codegen.Linkage.Areas as Linkage
import Native.Codegen.Linkage.Realised as Linkage
import Native.Codegen.Linkage.ResumePoint
import Native.Codegen.Linkage.Routine
import Native.Codegen.Linkage.Sym as Linkage
import Native.Codegen.LocatedIR.Block as LocatedIR
import Native.Codegen.LocatedIR.Cont as LocatedIR
import Native.Codegen.LocatedIR.Function as LocatedIR
import Native.Codegen.LocatedIR.Instr as LocatedIR
import Native.Codegen.LocatedIR.Label as LocatedIR
import Native.Codegen.LocatedIR.Location as LocatedIR
import Native.Codegen.LocatedIR.Mem as LocatedIR
import Native.Codegen.LocatedIR.Opnd as LocatedIR
import Native.Codegen.LocatedIR.Program as LocatedIR
import Native.Codegen.LocatedIR.Static as LocatedIR
import Native.Codegen.LocatedIR.Terminator as LocatedIR
import Native.Codegen.RegDesc
import Native.Codegen.RegMask
import Native.Codegen.Target
import Native.Data.LittleEndian
import Native.Data.Numbered
import Native.Data.Stateful as Data
import Native.HeapObj.LayoutWord
import Native.HeapObj.ValEnc
import Native.LiveTable
import Native.Primitive.DoubleBits
import Native.Rep
import Native.Types.Enc as Types
import Native.Types.Header as Types
import Native.Types.Kind as Types
import Native.Width

%default covering

||| What the rendering gives the linker once every function's code is
||| rendered: the program's read-only data, each item at its label, and the
||| per-thread areas its code uses.
public export
record Rendered where
  constructor MkRendered
  rodata : List (Asm.Label, List Datum)
  areas : Linkage.Areas

||| What the rendering knows of the program's names, which no step of it
||| changes: each function's label and each static's, and each function's
||| parameter types.
record Names (enc : Types.Enc) where
  constructor MkNames
  funs : SortedMap Name Asm.Label
  ||| Each function's parameter types: an immediate argument for a `Val` or a
  ||| `Fix` parameter is an integer, whose word the value encoding gives.
  params : SortedMap Name (List (IRCommon.Ty enc))
  statics : SortedMap Name Asm.Label

||| What the rendering makes as it goes, each step a new one: only what
||| changes, so that a step copies no more. Abstract: made and read by the
||| rendering alone.
export
record RS (enc : Types.Enc) where
  constructor MkRS
  nextLabel : Nat
  ||| The code so far of the function being rendered, accumulating at its
  ||| end.
  text : SnocList Asm.Instr
  ||| Slow paths, placed after the function being rendered.
  cold : SnocList Asm.Instr
  rodata : SnocList (Asm.Label, List Datum)
  ||| The most of each per-thread area the code so far uses.
  areas : Linkage.Areas
  ||| The registers the code written since the rendering of the current
  ||| instruction began writes, in `text` and `cold` (`Writes.writes`).
  written : RegSet

||| A program's rendering, a function at a time: the code the seed enters,
||| `main`, which jumps to the entry function, and the slow path the
||| allocation sites share (`mainCode`); then each
||| function's code, its slow paths after it (`functionCode`), each step
||| taking what the steps before it made and giving it on, so that each
||| function's code is a list of its own, to be encoded and forgotten
||| before the next is rendered; then the read-only data, the statics' last,
||| and the areas the code uses (`finished`).
public export
record Renderer (enc : Types.Enc) where
  constructor MkRenderer
  ||| The labels numbered before any function's code: each function's, each
  ||| static's and those of `mainCode`, and the seed's below them.
  labelsBefore : Nat
  mainCode : List Asm.Instr
  ||| What the rendering has made before the first function.
  first : RS enc
  ||| The program's functions, in the order their code goes.
  functions : List (LocatedIR.Function enc)
  functionCode : RS enc -> LocatedIR.Function enc -> Either String (RS enc, List Asm.Instr)
  finished : RS enc -> Either String Rendered

||| A target's allocatable registers as machine registers: each class's by
||| its index in the description, and all of them. Made once a function,
||| so that a set of allocatable registers (`RegMask`) becomes machine
||| registers without decoding a register's number.
record MachineRegs where
  constructor MkMachineRegs
  words : List RegSet
  floats : List RegSet
  registers : RegSet

-- Everything below renders for the program's encodings, and the contract as
-- the loaded runtime realises it. The value encoding decides how a `Val`
-- immediate and a fixnum are words, and the pointer tag every access
-- through a pointer folds into its displacement.

parameters (enc : Types.Enc) (realised : Linkage.Realised)
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

  ||| The whole program, a function at a time (`Renderer`): `main`, which
  ||| the seed enters, jumps to the entry function; every function follows;
  ||| the statics and crash messages are read-only data.
  export
  render : LocatedIR.Program enc -> Either String (Renderer enc)
  render p = do
    let start = Linkage.Sym.reservedLabels
        funs = fromList (zip (map (.name) p.functions) [start .. start + length p.functions])
        next1 = start + length p.functions
        statics = fromList (zip (map (.sym) p.statics) [next1 .. next1 + length p.statics])
        next2 = next1 + length p.statics
        symbols = Linkage.Routine.routineSymbols {enc} realised
    let params =
          fromList (map (\f => (f.name, map LocatedIR.Location.Place.ty f.params)) p.functions)
        names = MkNames funs params statics
        -- `idris_apply` stages a saturated closure's arguments in SCRATCH,
        -- and passes them as a call does, all `Val`s; a closure's arity is
        -- its function's number of parameters, and its function is CPS.
        arity = foldl max 0 [length f.params | f <- p.functions, f.conv == IRCommon.Conv.CPS]
        applyAreas =
          Linkage.MkAreas (Target.argsWords abi (replicate arity Rep.WordClass)) 0 arity 0
    (s, _) <- Data.Stateful.toEither $
      Data.Stateful.outcome (MkRS next2 [<] [<] [<] applyAreas RegSet.none) $
      do
      entry <- funLabel names p.entry
      emits [Asm.Lbl (sym Linkage.Sym.SymMain), Asm.Jmp entry]
      traverse_ sharedSlowPath [Width.Sub8, Width.Sub16, Width.Sub32]
    pure
      (MkRenderer s.nextLabel (s.text <>> []) ({ text := [<] } s) p.functions
         (functionCode names symbols) (finished names p.statics))
    where

      Render : Types.Enc -> Type -> Type
      Render enc = Data.Stateful (RS enc) String

      ||| The pointer tag of the value encoding: a pointer word is the object's
      ||| address plus it, so every load and store through a pointer folds its
      ||| negation into the displacement.
      ptag : Int
      ptag = cast (HeapObj.ValEnc.pointerTag enc.val)

      emit : Asm.Instr -> Render enc' ()
      emit i = Data.Stateful.modify { text $= (:< i), written $= RegSet.union (Writes.writes i) }

      -- the instructions put at the code's end in one step, not one each
      emits : List Asm.Instr -> Render enc ()
      emits is =
        Data.Stateful.modify
          { text $= (<>< is)
          , written $= \w => foldl (\v, i => RegSet.union (Writes.writes i) v) w is }

      ||| The slow path the allocation sites share, for live tables of the
      ||| width, with labels of its own.
      sharedSlowPath : Width.SubWord -> Render enc ()
      sharedSlowPath w = do
        first <-
          Data.Stateful.state
            (\s => ({ nextLabel := s.nextLabel + AllocLive.routineLabels } s, s.nextLabel))
        emits (AllocLive.routine w first)

      sym : Linkage.Sym -> Asm.Label
      sym = Linkage.Sym.label

      abi : Target.Abi
      abi = p.target.abi

      ||| The registers the located IR may name, by their index.
      allocatable : RegDesc
      allocatable = p.target.allocatable

      staticLabel : Names enc -> Name -> Render enc Asm.Label
      staticLabel names n = case lookup n names.statics of
        Just l => pure l
        Nothing => Data.Stateful.failWith ("no static " ++ show n)

      funLabel : Names enc -> Name -> Render enc Asm.Label
      funLabel names n = case lookup n names.funs of
        Just l => pure l
        Nothing => Data.Stateful.failWith ("no function " ++ show n)

      ||| A static's data: its header word, then a word for each field. A
      ||| uniform value's word is the value encoding's; another static's
      ||| address is a pointer word, tagged as the code's pointers to it are;
      ||| a function's entry address is untagged, as a closure's code word is.
      staticData : Names enc -> LocatedIR.Static enc -> Render enc (List Datum)
      staticData names s = do
        fields <- traverse field s.fields
        pure
          (Datum.Raw (Data.LittleEndian.le64 (cast (Types.Header.encodeHeader s.header))) :: fields)
        where
          field : LocatedIR.Static.SField -> Render enc Datum
          field (LocatedIR.Static.SWord w) = pure (Datum.Raw (Data.LittleEndian.le64 (cast w)))
          field (LocatedIR.Static.SVal i) = case HeapObj.ValEnc.valWord enc.val (cast i) of
            Just w => pure (Datum.Raw (Data.LittleEndian.le64 (cast w)))
            Nothing =>
              Data.Stateful.failWith
                ("the integer " ++ show i ++ ", in the static " ++ show s.sym ++
                                 ", which the value encoding has no word for")
          field (LocatedIR.Static.SRef t) = do l <- staticLabel names t
                                               pure (Datum.AddressOf l ptag)
          field (LocatedIR.Static.SCode f) = do l <- funLabel names f
                                                pure (Datum.AddressOf l 0)

      ||| A continuation's live values in the order it keeps them: the GC-visible
      ||| ones, which the collector forwards, then the raw ones, as its layout word
      ||| counts them. The resume block reloads them in the order its call stored
      ||| them.
      contFields : List (LocatedIR.Location.Place enc') ->
                   (List (LocatedIR.Location.Place enc'), List (LocatedIR.Location.Place enc'))
      contFields live =
        (filter (IRCommon.Ty.gcVisible . LocatedIR.Location.Place.ty) live,
         filter (not . IRCommon.Ty.gcVisible . LocatedIR.Location.Place.ty) live)

      ||| The description's registers as machine registers.
      machineRegs : RegDesc -> MachineRegs
      machineRegs d =
        let ws = map (RegSet.gpr . Asm.regOfNum) d.words
            fs = map (RegSet.xmm . Asm.xmmOfNum) d.floats
        in MkMachineRegs ws fs (foldl RegSet.union (foldl RegSet.union RegSet.none ws) fs)

      ||| The machine registers of a set of allocatable ones.
      machine : MachineRegs -> RegMask -> RegSet
      machine mr m = RegSet.union (from m.words mr.words) (from m.floats mr.floats)
        where
          from : Bits64 -> List RegSet -> RegSet
          from bits (r :: rs) =
            if bits == 0 then RegSet.none
              else RegSet.union (if bits .&. 1 == 0 then RegSet.none else r)
                     (from (prim__shr_Bits64 bits 1) rs)
          from _ [] = RegSet.none

      function : Names enc -> (symbols : SortedMap Name Linkage.Sym) ->
                 LocatedIR.Function enc -> Render enc ()
      function names symbols f = do
        fl <- funLabel names f.name
        labels <- traverse (\b => map (\l => (b.label, l)) fresh) f.blocks
        let table = fromList labels
            blk : LocatedIR.Label -> Asm.Label
            blk n = fromMaybe 0 (lookup n table)
        emits [Asm.Comment (show f.name), Asm.Lbl fl]
        -- a routine reached by symbol: the symbol is its entry too
        whenJust (lookup f.name symbols) $ \s =>
          emit (Asm.Lbl (sym s))
        -- the slots the function's registers take, counted once: CPS code's in
        -- SCRATCH, recorded; a Direct function's its frame, which the call
        -- pushed a word below, so an odd number of words keeps the stack
        -- 16-aligned inside; and below the stack limit, end the program
        let n = slots f
            frame = the Int $ case f.conv of
              IRCommon.Conv.Direct _ _ => 8 * cast (oddUp n)
              IRCommon.Conv.CPS => 0
        case f.conv of
          IRCommon.Conv.Direct _ _ =>
            emits [ Asm.AluI Asm.SUB Asm.RSP frame,
                   Asm.MovRM Asm.RAX (Asm.MRip (sym Linkage.Sym.SymStackLimit) 0),
                     Asm.Alu Asm.CMP Asm.RSP Asm.RAX
                                            , Asm.Jcc Asm.B (sym Linkage.Sym.SymStackOverflow) ]
          IRCommon.Conv.CPS => uses (Linkage.MkAreas 0 0 n 0)
        emits setBase
        takeValues f.params
        emit (Asm.Jmp (blk f.entry))
        -- bound once: an argument of a partial application is evaluated again
        -- at every call of it, which read the function's blocks once per block
        let rs = resumes f
            called = Target.callClobbers p.target
            mr = machineRegs allocatable
        traverse_ (block blk (IRCommon.Conv.results f.conv) frame rs called mr) f.blocks
        Data.Stateful.modify (\s => { text := s.text ++ s.cold, cold := [<] } s)
        where
          ||| The live values a resume block reloads, in the order its continuation
          ||| stores them, and the layout word for them.
          resumes : LocatedIR.Function enc ->
                    SortedMap LocatedIR.Label (List (LocatedIR.Location.Place enc), Integer)
          resumes f = fromList (mapMaybe resume f.blocks)
            where
              resume : LocatedIR.Block enc ->
                       Maybe (LocatedIR.Label, (List (LocatedIR.Location.Place enc), Integer))
              resume b = do
                c <- LocatedIR.Terminator.termCont b.term
                let (vals, raws) = contFields c.live
                pure (c.resume,
                  (vals ++ raws,
                   HeapObj.LayoutWord.layoutWord (cast (length vals)) (cast (length raws))))

          ||| Record that the code uses at least these areas.
          uses : Linkage.Areas -> Render enc ()
          uses a = Data.Stateful.modify { areas $= Linkage.Areas.maxAreas a }

          ||| The slots of `SCRATCH` a function's registers take: one past the
          ||| largest slot of a register it names, its parameters' and its
          ||| blocks' included.
          slots : LocatedIR.Function enc -> Nat
          slots f = foldl block (past 0 f.params) f.blocks
            where
              past : Nat -> List (LocatedIR.Location.Place enc) -> Nat
              past = foldl after
                where
                  after : Nat -> LocatedIR.Location.Place enc -> Nat
                  after n (LocatedIR.Location.At (LocatedIR.Location.Slot k _)) = max n (S k)
                  after n (LocatedIR.Location.At (LocatedIR.Location.Register _ _)) = n

              block : Nat -> LocatedIR.Block enc -> Nat
              block n b =
                past
                  (foldl (\m, i => past m (LocatedIR.Instr.instrRegs i)) (past n b.params) b.body)
                  (LocatedIR.Terminator.termRegs b.term)

          ||| Slot n of the function's slots.
          slotMem : Nat -> Asm.Mem
          slotMem n = Asm.MBase Asm.RBX (cast (Area.slotOffset (cast n)))

          ||| The machine register of the class's allocatable register at the
          ||| index.
          wordRegister : Nat -> Render enc Asm.Reg64
          wordRegister i = case getAt i allocatable.words of
            Just r => pure (Asm.regOfNum r)
            Nothing => Data.Stateful.failWith "a word register the target does not describe"

          floatRegister : Nat -> Render enc Asm.Xmm
          floatRegister i = case getAt i allocatable.floats of
            Just r => pure (Asm.xmmOfNum r)
            Nothing =>
              Data.Stateful.failWith "a floating-point register the target does not describe"

          ||| A location's word into the register, by `out`: from an XMM
          ||| register, a double's bits.
          getWordBy : (Asm.Instr -> Render enc ()) -> Asm.Reg64 -> LocatedIR.Location enc t ->
                      Render enc ()
          getWordBy out r (LocatedIR.Location.Slot n _) = out (Asm.MovRM r (slotMem n))
          getWordBy out r (LocatedIR.Location.Register i t) = case IRCommon.Ty.class t of
            Rep.WordClass => do
              s <- wordRegister i
              when (s /= r) $ out (Asm.MovRR r s)
            Rep.FloatClass => do
              x <- floatRegister i
              out (Asm.MovqRX r x)

          ||| The register's word into a location, by `out`: into an XMM
          ||| register, as a double's bits.
          putWordBy : (Asm.Instr -> Render enc ()) -> LocatedIR.Location enc t -> Asm.Reg64 ->
                      Render enc ()
          putWordBy out (LocatedIR.Location.Slot n _) r = out (Asm.MovMR (slotMem n) r)
          putWordBy out (LocatedIR.Location.Register i t) r = case IRCommon.Ty.class t of
            Rep.WordClass => do
              d <- wordRegister i
              when (d /= r) $ out (Asm.MovRR d r)
            Rep.FloatClass => do
              x <- floatRegister i
              out (Asm.MovqXR x r)

          getWord : Asm.Reg64 -> LocatedIR.Location enc t -> Render enc ()
          getWord r x = getWordBy emit r x

          store : LocatedIR.Location enc t -> Asm.Reg64 -> Render enc ()
          store d r = putWordBy emit d r

          ||| A location's double into the XMM register.
          getFloat : Asm.Xmm -> LocatedIR.Location enc t -> Render enc ()
          getFloat x (LocatedIR.Location.Slot n _) = emit (Asm.MovsdRM x (slotMem n))
          getFloat x (LocatedIR.Location.Register i _) = do
            s <- floatRegister i
            when (Asm.xmmNum s /= Asm.xmmNum x) $ emit (Asm.MovsdRR x s)

          ||| The XMM register's double into a location.
          putFloat : LocatedIR.Location enc t -> Asm.Xmm -> Render enc ()
          putFloat (LocatedIR.Location.Slot n _) x = emit (Asm.MovsdMR (slotMem n) x)
          putFloat (LocatedIR.Location.Register i _) x = do
            d <- floatRegister i
            when (Asm.xmmNum d /= Asm.xmmNum x) $ emit (Asm.MovsdRR d x)

          ||| A location's value into another of its class, of its type or, for
          ||| a retyping, of the type it is read as: directly when either is a
          ||| register. Never between two slots, which a move's row gives a
          ||| register for.
          move : LocatedIR.Location enc t -> LocatedIR.Location enc u -> Render enc ()
          move d x = case (d, x) of
            (LocatedIR.Location.Register i t, _) => case IRCommon.Ty.class t of
              Rep.FloatClass => do r <- floatRegister i; getFloat r x
              Rep.WordClass => do r <- wordRegister i; getWord r x
            (_, LocatedIR.Location.Register i t) => case IRCommon.Ty.class t of
              Rep.FloatClass => do r <- floatRegister i; putFloat d r
              Rep.WordClass => do r <- wordRegister i; store d r
            _ => Data.Stateful.failWith "a move between two slots"

          ||| The allocatable registers among the locations.
          registersIn : List (LocatedIR.Location.Place enc) -> RegMask
          registersIn = foldr add RegMask.none
            where
              add : LocatedIR.Location.Place enc -> RegMask -> RegMask
              add (LocatedIR.Location.At (LocatedIR.Location.Register i t)) m =
                RegMask.union (RegMask.single (IRCommon.Ty.class t) i) m
              add (LocatedIR.Location.At (LocatedIR.Location.Slot _ _)) m = m

          ||| Render an instruction or a terminator, `act`, and check what its
          ||| code writes of the allocatable registers (`mr`): the registers
          ||| `allowed`, its results' and those its row says it clobbers
          ||| (`X86.Rows`), no other, so that a value register allocation keeps
          ||| in any other is still there after.
          conforming : (mr : MachineRegs) -> (what : Lazy String) -> (allowed : Lazy RegMask) ->
                       Render enc () -> Render enc ()
          conforming mr what allowed act = do
            Data.Stateful.modify { written := RegSet.none }
            act
            s <- Data.Stateful.get
            let wrote = RegSet.intersection mr.registers s.written
            unless (RegSet.within wrote RegSet.none || RegSet.within wrote (machine mr allowed)) $
              Data.Stateful.failWith
                ("the rendering of " ++ what ++ " writes "
                 ++ fastConcat
                   (intersperse ", " (RegSet.names (RegSet.minus wrote (machine mr allowed))))
                 ++ ", which its row does not name")

          reg64 : Target.TargetReg -> Asm.Reg64
          reg64 = Asm.regOfNum

          xmm : Target.FloatReg -> Asm.Xmm
          xmm = Asm.xmmOfNum

          ||| Where values of the types travel between functions.
          placeTys : List (IRCommon.Ty enc) -> List Target.Loc
          placeTys tys = Target.place abi (map IRCommon.Ty.class tys)

          ||| Take values from where `place` puts them into the registers' slots: a
          ||| function's parameters on entry, or a direct call's results after it.
          ||| The registers first, then `ARGS`, through rax and rcx.
          takeValues : List (LocatedIR.Location.Place enc) -> Render enc ()
          takeValues ds = do
            let tys = map LocatedIR.Location.Place.ty ds
                items = zip (placeTys tys) ds
            uses (Linkage.MkAreas (Target.argsWords abi (map IRCommon.Ty.class tys)) 0 0 0)
            traverse_ (\(l, LocatedIR.Location.At d) => case l of
                         Target.InWordReg r => store d (reg64 r)
                         Target.InFloatReg f => putFloat d (xmm f)
                         Target.InArgs _ => pure ())
                      items
            traverse_ (\(l, LocatedIR.Location.At d) => case l of
                         Target.InArgs i => do
                           emit (Asm.Lea Asm.RAX (Asm.MRip (sym Linkage.Sym.SymArgs) 0))
                           emit (Asm.MovRM Asm.RCX (Asm.MBase Asm.RAX (cast (8 * i))))
                           store d Asm.RCX
                         _ => pure ())
                      items

          ||| Turn the object address in `s` into its pointer word in `d`.
          tagPointer : (d, s : Asm.Reg64) -> List Asm.Instr
          tagPointer d s = if ptag == 0 then (if d == s then [] else [Asm.MovRR d s])
            else [Asm.Lea d (Asm.MBase s ptag)]

          ||| The type two compared operands share: the register's, if either is one.
          pairTy : LocatedIR.Opnd enc t -> LocatedIR.Opnd enc t -> IRCommon.Ty enc
          pairTy (LocatedIR.Opnd.R x) _ = LocatedIR.Location.ty x
          pairTy _ (LocatedIR.Opnd.R y) = LocatedIR.Location.ty y
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
          loadAs : IRCommon.Ty enc -> Asm.Reg64 -> LocatedIR.Opnd enc t -> Render enc ()
          loadAs t r (LocatedIR.Opnd.Imm i) = emit (Asm.MovRI r (immWord t i))
          loadAs _ r (LocatedIR.Opnd.StaticRef s) = do l <- staticLabel names s
                                                       emit (Asm.Lea r (Asm.MRip l ptag))
          loadAs _ r (LocatedIR.Opnd.R x) = getWord r x

          ||| Load a raw operand.
          load : Asm.Reg64 -> LocatedIR.Opnd enc t -> Render enc ()
          load = loadAs IRCommon.Ty.W64

          loadReg : Asm.Reg64 -> LocatedIR.Location enc t -> Render enc ()
          loadReg r x = load r (LocatedIR.Opnd.R x)

          fitsImm32 : Integer -> Bool
          fitsImm32 i = i >= -2147483648 && i <= 2147483647

          ||| Compare rax with the operand, where a value of the type is expected:
          ||| `test` against the word 0, an immediate compare where the word fits.
          compareWith : IRCommon.Ty enc -> LocatedIR.Opnd enc t -> Render enc ()
          compareWith t (LocatedIR.Opnd.Imm c) =
            let w = immWord t c in
            if w == 0 then emit (Asm.Test Asm.RAX Asm.RAX)
            else if fitsImm32 w then emit (Asm.AluI Asm.CMP Asm.RAX (cast w))
            else emits [Asm.MovRI Asm.RCX w, Asm.Alu Asm.CMP Asm.RAX Asm.RCX]
          compareWith _ (LocatedIR.Opnd.R y) = do loadReg Asm.RCX y
                                                  emit (Asm.Alu Asm.CMP Asm.RAX Asm.RCX)
          compareWith _ (LocatedIR.Opnd.StaticRef s) = do l <- staticLabel names s
                                                          emits [Asm.Lea Asm.RCX (Asm.MRip l ptag),
                                                                 Asm.Alu Asm.CMP Asm.RAX Asm.RCX]

          coldEmit : Asm.Instr -> Render enc ()
          coldEmit i =
            Data.Stateful.modify { cold $= (:< i), written $= RegSet.union (Writes.writes i) }

          fresh : Render enc Asm.Label
          fresh = Data.Stateful.state (\s => ({ nextLabel := S s.nextLabel } s, s.nextLabel))

          isOdd : Nat -> Bool
          isOdd Z = False
          isOdd (S Z) = True
          isOdd (S (S n)) = isOdd n

          ||| The odd number at or just above `n`.
          oddUp : Nat -> Nat
          oddUp n = if isOdd n then n else S n

          ||| The live slots a call saves in `ROOTS`: the GC-visible ones across a
          ||| call that can collect, which the collector forwards there; none
          ||| across one that cannot. No callee writes its caller's slots, CPS
          ||| code's being in `SCRATCH` and a Direct function's in its own frame.
          saved : (collects : Bool) -> List (LocatedIR.Location.Place enc) ->
                  List (LocatedIR.Location.Place enc)
          saved False _ = []
          saved True live = filter (IRCommon.Ty.gcVisible . LocatedIR.Location.Place.ty) live

          ||| Save the live slots across a call in `ROOTS`, as `saved` chooses them.
          saveLive : (collects : Bool) -> (Asm.Instr -> Render enc ()) ->
                     List (LocatedIR.Location.Place enc) -> Render enc ()
          saveLive collects out live = do
            let gc = saved collects live
            uses (Linkage.MkAreas 0 (length gc) 0 0)
            when (not (null gc)) $ do
              out (Asm.Lea Asm.RSI (Asm.MRip (sym Linkage.Sym.SymNRoots) 0))
              out (Asm.MovRM Asm.RDX (Asm.MBase Asm.RSI 0))
              out (Asm.MovRR Asm.RCX Asm.RDX)
              out (Asm.ShiftI Asm.SHL Asm.RCX (cast Area.rootShift))
              out (Asm.Lea Asm.RDI (Asm.MRip (sym Linkage.Sym.SymRoots) 0))
              out (Asm.Alu Asm.ADD Asm.RDI Asm.RCX)
              traverse_
                (\(j, LocatedIR.Location.At r) => do
                   getWordBy out Asm.RCX r
                   out (Asm.MovMR (Asm.MBase Asm.RDI (cast (Area.rootOffset (cast j)))) Asm.RCX))
                (Data.Numbered.numbered gc)
              out (Asm.AluI Asm.ADD Asm.RDX (cast (length gc)))
              out (Asm.MovMR (Asm.MBase Asm.RSI 0) Asm.RDX)

          ||| The slots' base into rbx: `SCRATCH` for CPS code; for a Direct
          ||| function its frame, at the stack pointer its prologue left.
          setBase : List Asm.Instr
          setBase = case f.conv of
            IRCommon.Conv.CPS => [Asm.Lea Asm.RBX (Asm.MRip (sym Linkage.Sym.SymScratch) 0)]
            IRCommon.Conv.Direct _ _ => [Asm.MovRR Asm.RBX Asm.RSP]

          ||| Restore what `saveLive` saved, with rbx set, leaving rax alone.
          restoreLive : (collects : Bool) -> (Asm.Instr -> Render enc ()) ->
                        List (LocatedIR.Location.Place enc) -> Render enc ()
          restoreLive collects out live = do
            let gc = saved collects live
            when (not (null gc)) $ do
              out (Asm.Lea Asm.RSI (Asm.MRip (sym Linkage.Sym.SymNRoots) 0))
              out (Asm.MovRM Asm.RDX (Asm.MBase Asm.RSI 0))
              out (Asm.AluI Asm.SUB Asm.RDX (cast (length gc)))
              out (Asm.MovMR (Asm.MBase Asm.RSI 0) Asm.RDX)
              out (Asm.ShiftI Asm.SHL Asm.RDX (cast Area.rootShift))
              out (Asm.Lea Asm.RDI (Asm.MRip (sym Linkage.Sym.SymRoots) 0))
              out (Asm.Alu Asm.ADD Asm.RDI Asm.RDX)
              traverse_
                (\(j, LocatedIR.Location.At r) => do
                   out (Asm.MovRM Asm.RCX (Asm.MBase Asm.RDI (cast (Area.rootOffset (cast j)))))
                   putWordBy out r Asm.RCX)
                (Data.Numbered.numbered gc)

          ||| A site's cold code, at `slow`: the call of the slow path the sites
          ||| share, the jump back to `done` it returns to, and the site's live
          ||| table, of `live`'s slots, which the slow path saves across the
          ||| allocation.
          slowStub : (slow, done : Asm.Label) -> (live : List (LocatedIR.Location.Place enc)) ->
                     Render enc ()
          slowStub slow done live = do
            let gc = filter (IRCommon.Ty.gcVisible . LocatedIR.Location.Place.ty) live
                raw = filter (not . IRCommon.Ty.gcVisible . LocatedIR.Location.Place.ty) live
            uses (Linkage.MkAreas 0 (length gc) 0 0)
            -- the slow path saves slots: a value in a register across it is lost
            case (traverse LocatedIR.Location.Place.slotNumber gc,
                  traverse LocatedIR.Location.Place.slotNumber raw) of
              (Just gs, Just rs) => case LiveTable.table gs rs of
                Just t =>
                  Data.Stateful.modify { cold $= (<>< (Asm.Lbl slow :: AllocLive.stub done t)) }
                Nothing => Data.Stateful.failWith "a live table's entry needs more than 32 bits"
              _ => Data.Stateful.failWith "a register live across an allocation"

          ||| Allocate `bytes` into rax: the fast path inline, the shared slow path
          ||| called from the site's cold code, with `live` saved across it. The
          ||| fast path bumps r15 before it checks it against r14, so the slow path
          ||| finds the bytes as r15 less rax, and puts r15 back. Leaves rax
          ||| pointing at the uninitialised object.
          allocate : (bytes : Nat) -> (live : List (LocatedIR.Location.Place enc)) -> Render enc ()
          allocate bytes live = do
            slow <- fresh
            done <- fresh
            emits [ Asm.MovRR Asm.RAX Asm.R15, Asm.AluI Asm.ADD Asm.R15 (cast bytes),
                   Asm.Alu Asm.CMP Asm.R15 Asm.R14, Asm.Jcc Asm.A slow, Asm.Lbl done ]
            slowStub slow done live

          ||| Load an operand into a floating-point register: a slot's bits, or an
          ||| immediate's word, through rax.
          loadFloat : Asm.Xmm -> LocatedIR.Opnd enc t -> Render enc ()
          loadFloat x (LocatedIR.Opnd.R r) = getFloat x r
          loadFloat x (LocatedIR.Opnd.Imm i) =
            emits [Asm.MovRI Asm.RAX (cast i), Asm.MovqXR x Asm.RAX]
          loadFloat x (LocatedIR.Opnd.StaticRef _) =
            Data.Stateful.failWith "a static where a double is expected"

          ||| Pass values of the types where `place` puts them, for a call or a
          ||| return: `ARGS` first, through rax and rcx, then the floating-point
          ||| registers, then the word registers, since rcx is one of them.
          putValues : List (IRCommon.Ty enc) -> List (LocatedIR.Opnd.Arg enc) -> Render enc ()
          putValues tys xs = do
            uses (Linkage.MkAreas (Target.argsWords abi (map IRCommon.Ty.class tys)) 0 0 0)
            let items = zip3 (placeTys tys) tys xs
            traverse_ (\(l, t, LocatedIR.Opnd.MkArg x) => case l of
                         Target.InArgs i => do
                           emit (Asm.Lea Asm.RAX (Asm.MRip (sym Linkage.Sym.SymArgs) 0))
                           loadAs t Asm.RCX x
                           emit (Asm.MovMR (Asm.MBase Asm.RAX (cast (8 * i))) Asm.RCX)
                         _ => pure ())
                      items
            traverse_ (\(l, t, LocatedIR.Opnd.MkArg x) => case l of
                         Target.InFloatReg f => loadFloat (xmm f) x
                         _ => pure ())
                      items
            traverse_ (\(l, t, LocatedIR.Opnd.MkArg x) => case l of
                         Target.InWordReg r => loadAs t (reg64 r) x
                         _ => pure ())
                      items

          ||| A callee's parameter types, as its function in the program has them.
          ||| A callee that is no function of the program is an error, which each
          ||| call meets first, looking up its label (`funLabel`, `runtimeRoutine`).
          paramTys : Name -> Render enc (List (IRCommon.Ty enc))
          paramTys f =
            maybe (Data.Stateful.failWith ("no function " ++ show f)) pure (lookup f names.params)

          term : (LocatedIR.Label -> Asm.Label) -> (results : List (IRCommon.Ty enc)) ->
                 (frame : Int) -> LocatedIR.Terminator enc ->
                 Render enc ()
          term blk res frame terminator = case terminator of
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
                                                               (if HeapObj.ValEnc.fixnumTag enc.val
                                                                 == 0 then Asm.OR
                                                                else Asm.AND)
                                                              Asm.RAX Asm.RCX))
                                                               more
                                   emits [Asm.TestI Asm.RAX 1,
                                     Asm.Jcc
                                       (if HeapObj.ValEnc.fixnumTag enc.val == 0 then Asm.E
                                        else Asm.NE)
                                         (blk y),
                                          Asm.Jmp (blk n)]
            LocatedIR.Terminator.Branch r x y t f => do
                                   loadAs (pairTy x y) Asm.RAX x
                                   compareWith (pairTy x y) y
                                   emits [Asm.Jcc (cond r) (blk t), Asm.Jmp (blk f)]
            LocatedIR.Terminator.Switch r cs d => do
                                   loadReg Asm.RAX r
                                   -- each key an immediate of the scrutinee's type
                                   traverse_
                                     (\(v, l) => do
                                        compareWith (LocatedIR.Location.ty r)
                                          (LocatedIR.Opnd.Imm {t = IRCommon.Ty.W64} v)
                                        emit (Asm.Jcc Asm.E (blk l)))
                                     cs
                                   emit (Asm.Jmp (blk d))
            LocatedIR.Terminator.Call f args c => do
              l <- funLabel names f
              pushCont blk c (LocatedIR.Opnd.opsRegs args [])
              putValues !(paramTys f) args
              emit (Asm.Jmp l)
            LocatedIR.Terminator.TailCall f args => do
                                   l <- funLabel names f
                                   putValues !(paramTys f) args
                                   emit (Asm.Jmp l)
            LocatedIR.Terminator.Apply f x c => do
                                   pushCont blk c [LocatedIR.Location.At f, LocatedIR.Location.At x]
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
                                   Data.Stateful.modify { rodata $= (:< (l, [Datum.Raw bytes])) }
                                   emits [Asm.Lea Asm.RDI (Asm.MRip l 0),
                                          Asm.MovRI Asm.RSI (cast (length bytes)),
                                            Asm.Jmp (sym Linkage.Sym.SymCrash)]
            -- what is not lowered, and the function it stands in
            LocatedIR.Terminator.Unsupported what => do
                                   l <- fresh
                                   let bytes =
                                         map (cast . ord)
                                           (unpack
                                             ("idris: unsupported: " ++ what ++ ", in "
                                              ++ show f.name ++ "\n"))
                                   Data.Stateful.modify { rodata $= (:< (l, [Datum.Raw bytes])) }
                                   emits [Asm.Lea Asm.RDI (Asm.MRip l 0),
                                          Asm.MovRI Asm.RSI (cast (length bytes)),
                                            Asm.Jmp (sym Linkage.Sym.SymUnsupported)]
            LocatedIR.Terminator.Ret xs => do
              putValues res xs
              emits [Asm.AluI Asm.ADD Asm.RSP frame, Asm.Ret]
            t =>
              Data.Stateful.failWith
                ("the rendering does not support " ++ show (LocatedIR.Terminator.termName t)
                 ++ " yet")
            where
              ||| Allocate and initialise the continuation of a non-tail call, and make it
              ||| the current one. Its layout word counts fewer than 2^24 GC-visible and
              ||| fewer than 2^24 raw values (`layoutWord`); a continuation keeping more
              ||| is refused.
              pushCont : (LocatedIR.Label -> Asm.Label) -> LocatedIR.Cont enc ->
                         (alsoLive : List (LocatedIR.Location.Place enc)) -> Render enc ()
              pushCont blk c alsoLive = do
                let (vals, raws) = contFields c.live
                when (length vals >= 16777216 || length raws >= 16777216) $
                  Data.Stateful.failWith
                    "a continuation keeps more values than its layout word counts"
                -- the call's operands live across the allocation too, each once
                allocate (16 + 8 * length c.live) (c.live ++ besides c.live alsoLive)
                emits [ Asm.Lea Asm.RDX (Asm.MRip (blk c.resume) 0),
                       Asm.MovMR (Asm.MBase Asm.RAX 0) Asm.RDX
                      , Asm.MovMR (Asm.MBase Asm.RAX 8) Asm.R12 ]
                traverse_
                  (\(i, LocatedIR.Location.At r) => do
                     getWord Asm.RDX r
                     emit (Asm.MovMR (Asm.MBase Asm.RAX (cast (16 + 8 * i))) Asm.RDX))
                  (Data.Numbered.numbered (vals ++ raws))
                emits (tagPointer Asm.R12 Asm.RAX)
                where
                  -- the registers of `more` that are not in `live`, each once: the
                  -- slow path would save a register listed twice twice
                  besides : (live, more : List (LocatedIR.Location.Place enc)) ->
                            List (LocatedIR.Location.Place enc)
                  besides live [] = []
                  besides live (r :: rs) =
                    if any (\l => LocatedIR.Location.Place.key allocatable l
                                    == LocatedIR.Location.Place.key allocatable r) live
                      then besides live rs
                      else r :: besides (r :: live) rs

          block : (LocatedIR.Label -> Asm.Label) -> (results : List (IRCommon.Ty enc)) ->
                  (frame : Int) ->
                  SortedMap LocatedIR.Label (List (LocatedIR.Location.Place enc), Integer) ->
                  (called : RegMask) -> MachineRegs -> LocatedIR.Block enc -> Render enc ()
          block blk res frame rs called mr b = do
            case lookup b.label rs of
              Just (live, word) => do
                emits (Linkage.ResumePoint.resumePoint (blk b.label) word)
                emits setBase
                case reverse b.params of
                  (LocatedIR.Location.At result :: _) => store result Asm.RAX
                  [] => pure ()
                traverse_
                  (\(i, LocatedIR.Location.At r) => do
                     emit (Asm.MovRM Asm.RCX (Asm.MBase Asm.R12 (cast (16 + 8 * i) - ptag)))
                     store r Asm.RCX)
                  (Data.Numbered.numbered live)
                emit (Asm.MovRM Asm.R12 (Asm.MBase Asm.R12 (8 - ptag)))
              Nothing => emit (Asm.Lbl (blk b.label))
            traverse_
              (\i => conforming mr (LocatedIR.Instr.instrName i)
                       (RegMask.union (Rows.clobbers called i)
                         (registersIn (LocatedIR.Instr.results i)))
                       (instr blk i))
              b.body
            conforming mr (LocatedIR.Terminator.termName b.term)
              (Rows.termClobbers called b.term)
              (term blk res frame b.term)
            where
              instr : (LocatedIR.Label -> Asm.Label) -> LocatedIR.Instr enc -> Render enc ()
              instr blk instr' = case instr' of
                LocatedIR.Instr.Const d c => do emit
                                                  (Asm.MovRI Asm.RAX
                                                   (immWord (LocatedIR.Location.ty d) c))
                                                store d Asm.RAX
                LocatedIR.Instr.CodeOf d f => do l <- funLabel names f
                                                 emit (Asm.Lea Asm.RAX (Asm.MRip l 0))
                                                 store d Asm.RAX
                LocatedIR.Instr.StaticAddr d s => do l <- staticLabel names s
                                                     emit (Asm.Lea Asm.RAX (Asm.MRip l ptag))
                                                     store d Asm.RAX
                -- a byte address moved by a word: their sum
                LocatedIR.Instr.Offset d x y => do
                                  wordArith IRCommon.Op.Add x y Nothing
                                  store d Asm.RAX
                LocatedIR.Instr.Arith o d x y => do
                                  case LocatedIR.Location.ty d of
                                    IRCommon.Ty.Fix {fx} => fixArith o x y Nothing
                                    _ => wordArith o x y Nothing
                                  store d Asm.RAX
                -- `mul` multiplies rax by its operand into rdx:rax, the high word in rdx
                LocatedIR.Instr.Mul128 h l x y => do
                                  load Asm.RAX x
                                  load Asm.RCX y
                                  emit (Asm.Mul Asm.RCX)
                                  store h Asm.RDX
                                  store l Asm.RAX
                -- `div` divides rdx:rax by its operand, the quotient into rax and
                -- the remainder into rdx; a high word below the divisor, which
                -- the primitive's call proves, keeps it from faulting
                LocatedIR.Instr.Div128 q r h l x => do
                                  load Asm.RDX h
                                  load Asm.RAX l
                                  load Asm.RCX x
                                  emit (Asm.DivU Asm.RCX)
                                  store q Asm.RAX
                                  store r Asm.RDX
                LocatedIR.Instr.Unary o d x => do
                                  loadReg Asm.RAX x
                                  emit (case o of IRCommon.Op.Negate => Asm.Neg Asm.RAX
                                                  IRCommon.Op.Complement => Asm.Not Asm.RAX)
                                  store d Asm.RAX
                LocatedIR.Instr.ArithOv o d x y l => do
                                  case LocatedIR.Location.ty d of
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
                                  emits
                                    ([Asm.Alu Asm.ADD Asm.RAX Asm.RAX, Asm.Jcc Asm.O (blk l)]
                                     ++ addTag Asm.RAX)
                                  store d Asm.RAX
                -- A narrowing reads the low part of the slot, which a little-endian word
                -- keeps first, extending it as it loads.
                LocatedIR.Instr.Ext sw s d x => do
                                  case x of
                                    LocatedIR.Location.Slot n _ =>
                                      emit
                                        (Asm.Load (AccessWidth.accessWidth sw) s Asm.RAX
                                         (slotMem n))
                                    -- from a register, by shifting its low part to the top
                                    -- and back
                                    LocatedIR.Location.Register _ _ => do
                                      let by =
                                            the Bits8 (cast (minus 64 (8 * Width.subWordBytes sw)))
                                      getWord Asm.RAX x
                                      emits [ Asm.ShiftI Asm.SHL Asm.RAX by
                                            , Asm.ShiftI (if s then Asm.SAR else Asm.SHR) Asm.RAX
                                              by ]
                                  store d Asm.RAX
                LocatedIR.Instr.Move d x => move d x
                LocatedIR.Instr.Par _ =>
                  Data.Stateful.failWith "a parallel move the local assignment did not make moves"
                -- a retyping is a move: a pointer word and an address, a value
                -- and its word, are the same word
                LocatedIR.Instr.Narrow _ d x => move d x
                LocatedIR.Instr.Widen d x => move d x
                LocatedIR.Instr.AddrToWord d x => move d x
                LocatedIR.Instr.WordToAddr _ d x => move d x
                LocatedIR.Instr.ValToWord d x => move d x
                LocatedIR.Instr.WordToVal d x => move d x
                LocatedIR.Instr.LoadPart p d o => do
                                  loadReg Asm.RAX o
                                  emit
                                    (Asm.MovRM Asm.RAX
                                     (Asm.MBase Asm.RAX (negate (baseTag (LocatedIR.Mem.AtPtr o)))))
                                  emits
                                    (Asm.extractField Asm.RAX (cast (fst (Types.Header.place p)))
                                     (cast (snd (Types.Header.place p))))
                                  store d Asm.RAX
                LocatedIR.Instr.AllocObj {k} d h fs live => do
                                  if mutableKind k
                                     then allocateMutable
                                       (\r =>
                                         emit (Asm.MovRI r (cast (8 * Types.Header.objectWords h))))
                                         live
                                     else allocate (8 * Types.Header.objectWords h) live
                                  emits [Asm.MovRI Asm.RDX (cast (Types.Header.encodeHeader h)),
                                         Asm.MovMR (Asm.MBase Asm.RAX 0) Asm.RDX]
                                  let (from, count) = Types.Header.scanned h
                                      fieldTy : Nat -> IRCommon.Ty enc
                                      fieldTy i = if S i >= from && S i < from + count
                                        then IRCommon.Ty.Val
                                        else IRCommon.Ty.W64
                                  traverse_
                                    (\(i, LocatedIR.Opnd.MkArg f) => do
                                       loadAs (fieldTy i) Asm.RDX f
                                       emit
                                         (Asm.MovMR (Asm.MBase Asm.RAX (cast (8 * (S i)))) Asm.RDX))
                                    (Data.Numbered.numbered fs)
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
                                  Data.Stateful.modify { rodata $= (:< (msg, [Datum.Raw bytes])) }
                                  traverse_ coldEmit
                                    [ Asm.Lbl big, Asm.Lea Asm.RDI (Asm.MRip msg 0),
                                     Asm.MovRI Asm.RSI (cast (length bytes))
                                                     , Asm.Jmp (sym Linkage.Sym.SymCrash) ]
                                  loadReg Asm.RCX count
                                  emits
                                    [Asm.MovRI Asm.RDX
                                      (cast
                                        (prim__shl_Integer 1 (cast (snd (Types.Header.place p)))
                                         - 1)),
                                     Asm.Alu Asm.CMP Asm.RCX Asm.RDX, Asm.Jcc Asm.A big]
                                  size <- partSize p
                                  if mutableKind k
                                     then allocateMutable (\r => do getWord r count
                                                                    emits (size r)) live
                                     else allocateSized count size live
                                  loadReg Asm.RDX count
                                  emits
                                    [ Asm.ShiftI Asm.SHL Asm.RDX
                                     (cast (fst (Types.Header.place p))),
                                         Asm.AluI Asm.ADD Asm.RDX (cast (Types.Header.fixedWord k))
                                        , Asm.MovMR (Asm.MBase Asm.RAX 0) Asm.RDX ]
                                  case fill of
                                    Nothing => pure ()
                                    Just f => do
                                      loop <- fresh
                                      end <- fresh
                                      loadReg Asm.RCX count
                                      loadAs IRCommon.Ty.Val Asm.RDX f
                                      emits [ Asm.Lea Asm.RDI (Asm.MBase Asm.RAX 8),
                                             Asm.Lbl loop, Asm.Test Asm.RCX Asm.RCX,
                                               Asm.Jcc Asm.E end
                                            , Asm.MovMR (Asm.MBase Asm.RDI 0) Asm.RDX,
                                              Asm.AluI Asm.ADD Asm.RDI 8,
                                              Asm.AluI Asm.SUB Asm.RCX 1, Asm.Jmp loop,
                                                Asm.Lbl end ]
                                  emits (tagPointer Asm.RAX Asm.RAX)
                                  store d Asm.RAX
                LocatedIR.Instr.DirectCall f args ds collects live => do
                                  callee <- maybe (runtimeRoutine f) pure (lookup f names.funs)
                                  tys <- paramTys f
                                  saveLive collects emit live
                                  putValues tys args
                                  emit (Asm.Call callee)
                                  emits setBase
                                  takeValues ds
                                  restoreLive collects emit live
                LocatedIR.Instr.Convert IRCommon.Op.I2F d x => do
                                  loadReg Asm.RAX x
                                  emit (Asm.Cvtsi2sd Asm.XMM0 Asm.RAX)
                                  putFloat d Asm.XMM0
                LocatedIR.Instr.Convert IRCommon.Op.F2I d x => do
                                  getFloat Asm.XMM0 x
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
                                  emit
                                    (Asm.MovRI Asm.RAX (cast (Primitive.DoubleBits.doubleBits x)))
                                  store d Asm.RAX
                LocatedIR.Instr.FNeg d x => do
                                  loadReg Asm.RAX x
                                  emits [Asm.MovRI Asm.RCX 0x8000000000000000,
                                         Asm.Alu Asm.XOR Asm.RAX Asm.RCX]
                                  store d Asm.RAX
                LocatedIR.Instr.FSqrt d x => do
                                  loadFloat Asm.XMM0 (LocatedIR.Opnd.R x)
                                  emit (Asm.Sse Asm.SQRTSD Asm.XMM0 Asm.XMM0)
                                  putFloat d Asm.XMM0
                LocatedIR.Instr.FArith o d x y => do
                                  loadFloat Asm.XMM0 (LocatedIR.Opnd.R x)
                                  loadFloat Asm.XMM1 (LocatedIR.Opnd.R y)
                                  emit
                                    (Asm.Sse (case o of IRCommon.Op.FAdd => Asm.ADDSD
                                                        IRCommon.Op.FSub => Asm.SUBSD
                                                        IRCommon.Op.FMul => Asm.MULSD
                                                        IRCommon.Op.FDiv =>
                                                          Asm.DIVSD) Asm.XMM0 Asm.XMM1)
                                  putFloat d Asm.XMM0
                -- `ucomisd a, b` sets the flags as an unsigned comparison of a with b,
                -- and all of ZF, PF and CF when either is a NaN. So x < y is y above x and
                -- x <= y is y above or equal to x, which the NaN case fails; equality also
                -- needs PF clear, and inequality holds when PF is set.
                LocatedIR.Instr.FCmp r d x y => do
                                  emits [Asm.Alu Asm.XOR Asm.RDX Asm.RDX,
                                         Asm.Alu Asm.XOR Asm.RCX Asm.RCX]
                                  loadFloat Asm.XMM0 (LocatedIR.Opnd.R x)
                                  loadFloat Asm.XMM1 (LocatedIR.Opnd.R y)
                                  emits $ case r of
                                    IRCommon.Op.EqR =>
                                      [Asm.Ucomisd Asm.XMM0 Asm.XMM1, Asm.Setcc Asm.E Asm.RDX,
                                        Asm.Setcc Asm.NP Asm.RCX,
                                       Asm.Alu Asm.AND Asm.RDX Asm.RCX]
                                    IRCommon.Op.NeR =>
                                      [Asm.Ucomisd Asm.XMM0 Asm.XMM1, Asm.Setcc Asm.NE Asm.RDX,
                                        Asm.Setcc Asm.P Asm.RCX,
                                       Asm.Alu Asm.OR Asm.RDX Asm.RCX]
                                    IRCommon.Op.LtS =>
                                      [Asm.Ucomisd Asm.XMM1 Asm.XMM0, Asm.Setcc Asm.A Asm.RDX]
                                    IRCommon.Op.LtU =>
                                      [Asm.Ucomisd Asm.XMM1 Asm.XMM0, Asm.Setcc Asm.A Asm.RDX]
                                    IRCommon.Op.LeS =>
                                      [Asm.Ucomisd Asm.XMM1 Asm.XMM0, Asm.Setcc Asm.AE Asm.RDX]
                                    IRCommon.Op.LeU =>
                                      [Asm.Ucomisd Asm.XMM1 Asm.XMM0, Asm.Setcc Asm.AE Asm.RDX]
                                    IRCommon.Op.GtS =>
                                      [Asm.Ucomisd Asm.XMM0 Asm.XMM1, Asm.Setcc Asm.A Asm.RDX]
                                    IRCommon.Op.GtU =>
                                      [Asm.Ucomisd Asm.XMM0 Asm.XMM1, Asm.Setcc Asm.A Asm.RDX]
                                    IRCommon.Op.GeS =>
                                      [Asm.Ucomisd Asm.XMM0 Asm.XMM1, Asm.Setcc Asm.AE Asm.RDX]
                                    IRCommon.Op.GeU =>
                                      [Asm.Ucomisd Asm.XMM0 Asm.XMM1, Asm.Setcc Asm.AE Asm.RDX]
                                  store d Asm.RDX
                LocatedIR.Instr.LoadN sw s d m => do
                                  address Asm.RAX m (Width.subWordBytes sw)
                                  emit
                                    (Asm.Load (AccessWidth.accessWidth sw) s Asm.RCX
                                     (Asm.MBase Asm.RAX (m.offset - baseTag m.base)))
                                  store d Asm.RCX
                LocatedIR.Instr.StoreN sw m x => do
                                  address Asm.RAX m (Width.subWordBytes sw)
                                  loadReg Asm.RCX x
                                  emit
                                    (Asm.Store (AccessWidth.accessWidth sw)
                                     (Asm.MBase Asm.RAX (m.offset - baseTag m.base)) Asm.RCX)
                LocatedIR.Instr.AreaAddr d a => do
                                  emit (Asm.Lea Asm.RAX (Asm.MRip (sym (Linkage.Sym.areaSym a)) 0))
                                  store d Asm.RAX
                -- the pinned registers: the allocation window and the current continuation
                LocatedIR.Instr.GetPinned r d => store d (pinnedReg r)
                LocatedIR.Instr.SetPinned r x => load (pinnedReg r) x
                -- Linux's system call on x86-64: the number in rax, the arguments in rdi,
                -- rsi, rdx, r10, r8 and r9, the result in rax; the kernel keeps every
                -- register but rcx and r11
                LocatedIR.Instr.SystemCall d (n :: args) =>
                  if length args > 6
                    then Data.Stateful.failWith "a system call of more than six arguments"
                    else do
                    traverse_ (\(r, x) => load r x)
                      (zip [Asm.RDI, Asm.RSI, Asm.RDX, Asm.R10, Asm.R8, Asm.R9] args)
                    load Asm.RAX n
                    emits [Asm.Syscall]
                    store d Asm.RAX
                LocatedIR.Instr.Loc _ => pure ()
                LocatedIR.Instr.Comment s => emit (Asm.Comment s)
                i =>
                  Data.Stateful.failWith
                    ("the rendering does not support " ++ LocatedIR.Instr.instrName i ++ " yet")
                where
                  -- The register each pinned register is.
                  pinnedReg : IRCommon.Pinned -> Asm.Reg64
                  pinnedReg IRCommon.Pinned.Hp = Asm.R15
                  pinnedReg IRCommon.Pinned.HpLim = Asm.R14
                  pinnedReg IRCommon.Pinned.K = Asm.R12

                  -- The bytes of an object of `r` bytes of data: the header word, then the
                  -- data rounded up to words.
                  bytesSize : Asm.Reg64 -> List Asm.Instr
                  bytesSize r =
                    [Asm.AluI Asm.ADD r 15, Asm.ShiftI Asm.SHR r 3, Asm.ShiftI Asm.SHL r 3]

                  -- The object's bytes, from the count in `r`: the header word, then the
                  -- elements as words, or the bytes rounded up to words.
                  partSize : Types.Header.HeaderPart k' -> Render enc (Asm.Reg64 -> List Asm.Instr)
                  partSize Types.Header.ArrayElemsP =
                    pure (\r => [Asm.ShiftI Asm.SHL r 3, Asm.AluI Asm.ADD r 8])
                  -- a string made by its count is not known to be ASCII: its bit is 0,
                  -- which only costs the fast paths
                  partSize Types.Header.StringBytesP = pure bytesSize
                  partSize Types.Header.StringCharsP =
                    pure (\r => Asm.ShiftI Asm.SHL r 2 :: bytesSize r)
                  partSize Types.Header.BytesLengthP = pure bytesSize
                  partSize q =
                    Data.Stateful.failWith ("AllocSized cannot size an object by " ++ show q)

                  ||| Allocate an object whose size depends on `count`, as `allocate` does a
                  ||| fixed one: `size r` turns the count in `r` into the object's bytes.
                  ||| Leaves rax pointing at the uninitialised object.
                  allocateSized : (count : LocatedIR.Location enc t) ->
                                  (size : Asm.Reg64 -> List Asm.Instr) ->
                                  (live : List (LocatedIR.Location.Place enc)) -> Render enc ()
                  allocateSized count size live = do
                    slow <- fresh
                    done <- fresh
                    loadReg Asm.RDX count
                    emits (size Asm.RDX)
                    emits [ Asm.MovRR Asm.RAX Asm.R15, Asm.Alu Asm.ADD Asm.R15 Asm.RDX,
                           Asm.Alu Asm.CMP Asm.R15 Asm.R14, Asm.Jcc Asm.A slow, Asm.Lbl done ]
                    slowStub slow done live

                  ||| A callee of a direct call that is no function of the program: an
                  ||| error, which names it. The lowering declares outside the program
                  ||| each routine of the runtime it calls by name whose form it is not
                  ||| given (`Lower.lowerProgram`), so a call of one ends here, and the
                  ||| compile with it.
                  runtimeRoutine : Name -> Render enc Asm.Label
                  runtimeRoutine n = Data.Stateful.failWith ("no runtime routine " ++ show n)

                  ||| What a load or store through the base subtracts: the pointer tag if
                  ||| it is a pointer word, nothing if it is a byte address.
                  baseTag : LocatedIR.Mem.Base enc -> Int
                  baseTag (LocatedIR.Mem.AtPtr _) = ptag
                  baseTag (LocatedIR.Mem.AtBytes _) = 0

                  ||| Arithmetic on raw words, into rax.
                  wordArith : IRCommon.Op.ArithOp -> LocatedIR.Opnd enc t -> LocatedIR.Opnd enc u ->
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
                      IRCommon.Op.RemS =>
                        emits [Asm.Cqo, Asm.Idiv Asm.RCX, Asm.MovRR Asm.RAX Asm.RDX]
                      IRCommon.Op.DivU => emits [Asm.Alu Asm.XOR Asm.RDX Asm.RDX, Asm.DivU Asm.RCX]
                      IRCommon.Op.RemU =>
                        emits [Asm.Alu Asm.XOR Asm.RDX Asm.RDX,
                               Asm.DivU Asm.RCX, Asm.MovRR Asm.RAX Asm.RDX]
                    maybe (pure ()) (\l => emit (Asm.Jcc Asm.O l)) ov

                  ||| Turn twice a value, in the register, into the fixnum's word: `or` in
                  ||| the fixnum tag, since the low bit is clear.
                  addTag : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} -> Asm.Reg64 ->
                           List Asm.Instr
                  addTag r = if HeapObj.ValEnc.fixnumTag enc.val == 0 then []
                    else [Asm.AluI Asm.OR r (cast (HeapObj.ValEnc.fixnumTag enc.val))]

                  ||| Arithmetic on fixnums, into rax, computed on their words. Where fixnum n
                  ||| is the word w(n) = 2n + t, for the value encoding's fixnum tag t: x + y is
                  ||| w(x) + 2y, x - y is w(x) - 2y and x xor y is w(x) xor 2y; x and y and
                  ||| x or y are the words' own; x * y is 2x * y, then plus t. Each addition,
                  ||| subtraction and multiplication overflows exactly when its result is
                  ||| outside the fixnum range. A shift has no such identity: it takes the
                  ||| values, shifts and tags.
                  fixArith : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} ->
                             IRCommon.Op.ArithOp ->
                             LocatedIR.Opnd enc t -> LocatedIR.Opnd enc t ->
                             (overflow : Maybe Asm.Label) -> Render enc ()
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
                      _ =>
                        Data.Stateful.failWith
                          ("the rendering does not support " ++ show o ++ " yet")
                    where
                      jo : Render enc ()
                      jo = maybe (pure ()) (\l => emit (Asm.Jcc Asm.O l)) ov
                      retag : Render enc ()
                      retag = emits (addTag Asm.RAX)
                      ||| Load a fixnum's value.
                      loadValue : Asm.Reg64 -> LocatedIR.Opnd enc t -> Render enc ()
                      loadValue r (LocatedIR.Opnd.Imm c) = emit (Asm.MovRI r (cast c))
                      loadValue r (LocatedIR.Opnd.StaticRef _) =
                        Data.Stateful.failWith "a static where a fixnum is expected"
                      loadValue r (LocatedIR.Opnd.R x) = do loadReg r x
                                                            emit (Asm.ShiftI Asm.SAR r 1)

                      shift : Asm.ShiftOp -> Render enc ()
                      shift sh = do
                        loadValue Asm.RAX x
                        loadValue Asm.RCX y
                        emits [Asm.ShiftCl sh Asm.RAX, Asm.ShiftI Asm.SHL Asm.RAX 1]
                        retag

                      ||| Load twice a fixnum's value: its word less the fixnum tag, or an
                      ||| immediate doubled.
                      loadTwice : Asm.Reg64 -> LocatedIR.Opnd enc t -> Render enc ()
                      loadTwice r (LocatedIR.Opnd.Imm c) = emit (Asm.MovRI r (2 * cast c))
                      loadTwice r (LocatedIR.Opnd.StaticRef _) =
                        Data.Stateful.failWith "a static where a fixnum is expected"
                      loadTwice r (LocatedIR.Opnd.R x) = do
                        loadReg r x
                        when (HeapObj.ValEnc.fixnumTag enc.val /= 0) $
                          emit (Asm.AluI Asm.SUB r (cast (HeapObj.ValEnc.fixnumTag enc.val)))

                      ||| `op` of rax and twice the operand's value, an immediate folded into the
                      ||| instruction where it fits.
                      aluTwice : Asm.AluOp -> LocatedIR.Opnd enc t -> Render enc ()
                      aluTwice op (LocatedIR.Opnd.Imm c) =
                        let v = 2 * cast c in
                        if fitsImm32 v then emit (Asm.AluI op Asm.RAX (cast v))
                          else emits [Asm.MovRI Asm.RCX v, Asm.Alu op Asm.RAX Asm.RCX]
                      aluTwice op y = do loadTwice Asm.RCX y; emit (Asm.Alu op Asm.RAX Asm.RCX)

                  ||| The kinds whose objects hold values the collector follows and are
                  ||| written after they are made. They are allocated by a call to
                  ||| `idris_alloc_mutable`, never by the inline bump, so that a collector
                  ||| with a nursery can keep them out of it, and then a write into an old
                  ||| object never makes it point into the nursery. A raw object (`BYTES`)
                  ||| may be written too, but holds no pointer, so the bump serves it.
                  mutableKind : Types.Kind -> Bool
                  mutableKind Types.Kind.IOREF = True
                  mutableKind Types.Kind.ARRAY = True
                  mutableKind Types.Kind.STRUCT = True
                  mutableKind _ = False

                  ||| Allocate a mutable object of the bytes `bytesInto` computes into a
                  ||| register, by a call to `idris_alloc_mutable` with `live` saved across it.
                  ||| Leaves rax pointing at the uninitialised object.
                  allocateMutable : (bytesInto : Asm.Reg64 -> Render enc ()) ->
                                    (live : List (LocatedIR.Location.Place enc)) ->
                                    Render enc ()
                  allocateMutable bytesInto live = do
                    saveLive True emit live
                    bytesInto Asm.RDI
                    emit (Asm.Call (sym Linkage.Sym.SymAllocMutable))
                    emit (Asm.MovRR Asm.RAX Asm.RDI)
                    emits setBase
                    restoreLive True emit live

                  ||| The base of a memory operand into `r`, plus its index scaled by `width`,
                  ||| the access's width in bytes: an address that lives only within the
                  ||| instruction that computes it.
                  address : Asm.Reg64 -> LocatedIR.Mem enc -> (width : Nat) -> Render enc ()
                  address r m width = do
                    case m.base of
                      LocatedIR.Mem.AtBytes b => loadReg r b
                      LocatedIR.Mem.AtPtr b => loadReg r b
                    case m.index of
                      Nothing => pure ()
                      Just i => do loadReg Asm.RDX i
                                   emits [Asm.ShiftI Asm.SHL Asm.RDX (shiftFor width),
                                          Asm.Alu Asm.ADD r Asm.RDX]
                    where
                      shiftFor : Nat -> Bits8
                      shiftFor 1 = 0
                      shiftFor 2 = 1
                      shiftFor 4 = 2
                      shiftFor _ = 3

      -- a function's code, its slow paths after it, rendered after what
      -- the rendering has made
      functionCode : Names enc -> (symbols : SortedMap Name Linkage.Sym) -> RS enc ->
                     LocatedIR.Function enc -> Either String (RS enc, List Asm.Instr)
      functionCode names symbols s f = do
        (s', _) <- Data.Stateful.toEither (Data.Stateful.outcome s (function names symbols f))
        pure ({ text := [<] } s', s'.text <>> [])

      -- the statics' data after what the rendering has made: the read-only
      -- data and the areas
      finished : Names enc -> List (LocatedIR.Static enc) -> RS enc -> Either String Rendered
      finished names statics s = do
        (s', _) <- Data.Stateful.toEither $ Data.Stateful.outcome s $
          traverse_ (\st => do l <- staticLabel names st.sym
                               pieces <- staticData names st
                               Data.Stateful.modify { rodata $= (:< (l, pieces)) })
            statics
        pure (MkRendered (s'.rodata <>> []) s'.areas)
