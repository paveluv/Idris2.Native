-- The slow path of an allocation of a fixed size keeps every register: a
-- value may stay in one across an allocation, and the collector moving
-- the object a GC-visible one points to leaves it pointing at the copy.
--
-- The program, as the Idris
--
--     keep : a -> a
--     keep x = let a = 1001; b = 2002; ...; g = 7007   -- seven words
--                  z = 2.5                              -- a double
--                  p = MkBox x                          -- an object
--                  _ = MkBox 0       -- an allocation, with all of them live
--              in if a .. g, z and p's field are as made then 0 else crash
--
-- is built in the term IR and allocated as the code generator allocates
-- it, a slot for every value; then the words are moved, each where it is
-- made, into rsi, rdi, r8 to r11 and r13, the double into xmm3, and the
-- object into rbp, and read from there after the allocation. The value
-- check accepts that program: a register survives an allocation of a
-- fixed size, the GC-visible ones listed in its live list, which its table
-- then names by their words in SAVE. Each allocation takes the slow path
-- (an 8-byte window), whose stand-in for the runtime's `allocSlow` writes
-- junk into r13, rbp and xmm3, its system calls into the argument
-- registers and rcx and r11, and moves every object a root points to,
-- poisoning the old one: a register the slow path does not restore, or a
-- root it does not reload into its register, fails the check after.
--
-- The program prints its value check's verdict and `keep`'s tables, and
-- exits with 0 when every value came back. Checked to fail when the slow
-- path restores no floating-point register, and when it reloads no root;
-- without its word registers' restores, the slow path is refused at link
-- time, since it would change registers its contract says it keeps.
module Main

import Core.Name
import Core.Name.Namespace
import Data.Fin
import Data.IORef
import Data.List
import Data.List.Quantifiers
import Data.So
import Data.SortedMap
import Data.SortedSet
import Native.AllocationMargin
import Native.Area
import Native.Codegen.ELF
import Native.Codegen.IRCommon.ConIds
import Native.Codegen.IRCommon.Conv
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Pinned
import Native.Codegen.IRCommon.Ty
import Native.Codegen.Link
import Native.Codegen.Linkage.Realised
import Native.Codegen.Linkage.Routine
import Native.Codegen.Linkage.RuntimeModule
import Native.Codegen.Linkage.Sym
import Native.Codegen.LocalAssign
import Native.Codegen.LocatedIR.Block
import Native.Codegen.LocatedIR.Function
import Native.Codegen.LocatedIR.Instr
import Native.Codegen.LocatedIR.Label
import Native.Codegen.LocatedIR.Location
import Native.Codegen.LocatedIR.Program
import Native.Codegen.LocatedIR.Step
import Native.Codegen.RegAlloc
import Native.Codegen.RegMask
import Native.Codegen.Target
import Native.Codegen.TermIR.Body
import Native.Codegen.TermIR.Build
import Native.Codegen.TermIR.Decls
import Native.Codegen.TermIR.Def
import Native.Codegen.TermIR.FieldTys
import Native.Codegen.TermIR.Instr
import Native.Codegen.TermIR.IsInt
import Native.Codegen.TermIR.Mem
import Native.Codegen.TermIR.Opnd
import Native.Codegen.TermIR.Program
import Native.Codegen.TermIR.Sig
import Native.Codegen.TermIR.Sizes
import Native.Codegen.TermIR.StaticDef
import Native.Codegen.TermIR.StaticSig
import Native.Codegen.TermIR.Var
import Native.Codegen.ValueCheck
import Native.Codegen.X86.Asm
import Native.Codegen.X86.Assembler
import Native.Codegen.X86.Encode
import Native.Codegen.X86.Render
import Native.Codegen.X86.Rows
import Native.Codegen.X86.Target
import Native.Data.Distinct
import Native.HeapObj.Shape
import Native.HeapObj.ValEnc
import Native.Intrinsic
import Native.LiveTable
import Native.Port
import Native.Primitive
import Native.Routine
import Native.Types.BignumEnc
import Native.Types.Enc
import Native.Types.Header
import Native.Types.IntegerRoutine
import Native.Types.Kind
import Native.Types.StringEnc
import Native.Types.StringRoutine
import Native.Width

%default total

||| The default encodings, with fixnum tag 1: a fixnum n is the word 2n + 1.
TestEnc : Enc
TestEnc = defaultEnc

nm : String -> Name
nm s = NS (mkNamespace "Main") (UN (Basic s))

-- The runtime's routines this program writes itself, under the runtime's
-- names, as native/term001 does.
runtimeStart, runtimeAllocSlow, runtimeAllocMutable, runtimeCrash : Name
runtimeStart = NS (runtimeModule "Start") (UN (Basic "start"))
runtimeAllocSlow = NS (runtimeModule "Space") (UN (Basic "allocSlow"))
runtimeAllocMutable = NS (runtimeModule "Space") (UN (Basic "allocMutable"))
runtimeCrash = NS (runtimeModule "System") (UN (Basic "crash"))

realised : Realised
realised =
  MkRealised [(runtimeStart, Start),
              (runtimeAllocSlow, AllocSlow), (runtimeAllocMutable, AllocMutable),
              (runtimeCrash, Crash)]
             Nothing Nothing empty empty empty empty


T : Decls TestEnc
T = MkDecls
  [ MkSig (nm "main") CPS [] False
  , MkSig (nm "keep") CPS [Val] False
  , MkSig (flatName runtimeCrash) (Direct [] False) [W64, W64] False
  , MkSig (flatName runtimeStart) (Direct [] False) [W64, W64] False
  , MkSig (flatName runtimeAllocSlow) (Direct [W64] False) [W64] False
  , MkSig (flatName runtimeAllocMutable) (Direct [W64] False) [W64] False ]
  []

keepRef : Var (sigs T) (MkSig (nm "keep") CPS [Val] False)
keepRef = later here

||| A fixnum's word.
untagged : Opnd vr Val -> Build T c False vr l (Opnd vr W64)
untagged v = do
  f <- emit1 (NarrowFix v)
  emit1 (Untag f)

||| The words of `keep`, each held in a register of its own.
held : List Integer
held = [1001, 2002, 3003, 4004, 5005, 6006, 7007]

||| The words, each made by an addition, so that each is a value of its own.
made : List Integer -> Build T CPS False vr l (List (Opnd vr W64))
made [] = pure []
made (n :: ns) = do
  w <- emit1 (Arith Add (W (cast n - 1)) (W 1))
  rest <- made ns
  pure (w :: rest)

||| Every word's difference from its number, or-ed together: 0 when each is
||| its own.
differences : List (Opnd vr W64, Integer) -> Build T CPS False vr l (Opnd vr W64)
differences [] = pure (W 0)
differences ((w, n) :: rest) = do
  d <- emit1 (Arith Xor w (W (cast n)))
  r <- differences rest
  emit1 (Arith Or d r)

||| `keep x`: words, a double and an object made, then an allocation with
||| all of them live, then whether each is as made, its object's field `x`.
keepBody : Closed T CPS False [Val]
keepBody = build $ \[x] => do
  ws <- made held
  z <- emit1 (FConst 2.5)
  p <- emit1 (AllocObj (ConH 0 1) [x])
  pv <- emit1 (WidenPtr p)
  _ <- emit1 (AllocObj (ConH 0 1) [Vx {enc = TestEnc} 0])
  -- every difference from what was made, or-ed together: 0 when all are
  wrong <- differences (zip ws held)
  two <- emit1 (FConst 2.5)
  zw <- emit1 (FCmp NeR z two)
  field <- emit1 (Load Val (MkMem (AtPtr p) Nothing 8))
  fw <- untagged field
  fd <- emit1 (Arith Xor fw (W 7))
  all1 <- emit1 (Arith Or wrong zw)
  all2 <- emit1 (Arith Or all1 fd)
  leaveIf NeR all2 (W 0) (crash "keep: a value not kept across the allocation")
  return (Vx {enc = TestEnc} 0)

mainBody : Closed T CPS False []
mainBody = build $ \[] => do
  r <- call keepRef [Vx {enc = TestEnc} 7]
  rw <- untagged r
  leaveIf NeR rw (W 0) (crash "keep: not 0")
  return (Vx {enc = TestEnc} 0)
||| The runtime's `start`, reduced to what this program needs: the first
||| allocation window, mapped, of `window` bytes.
startBody : Closed T (Direct [] False) False [W64, W64]
startBody = build $ \[entry, window] => do
  -- mmap(NULL, window, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0)
  w <- emit1 (SystemCall 6 [W 9, W 0, window, W 3, W 0x22, W (-1), W 0])
  base <- emit1 (WordToByteAddr w)
  emit0 (SetPinned Hp base)
  lim <- emit1 (Offset base window)
  emit0 (SetPinned HpLim lim)
  ret []

||| The runtime's allocation slow path, reduced to what this program needs,
||| junk first in registers `keep` holds its values in that the system calls
||| below leave alone (r13 and rbp, and xmm3: `junked`), then a collection
||| that moves every object `ROOTS` points to: a copy of
||| its two words in memory fresh from the system, its old field poisoned,
||| the root pointed at the copy. Then `bytes` fresh from the system and the
||| allocation margin past them, the object at their start, the window left
||| empty, so that the next allocation comes here too.
allocSlowBody : Closed T (Direct [W64] False) False [W64]
allocSlowBody = build $ \[bytes] => do
  _ <- emit1 (Arith Add (W 0x5eed) bytes)
  _ <- emit1 (Arith Add (W 0x7eed) bytes)
  _ <- emit1 (FConst 99.5)
  roots <- emit1 (AreaAddr ROOTS)
  nrootsAt <- emit1 (AreaAddr NROOTS)
  n <- emit1 (Load W64 (MkMem (AtBytes nrootsAt) Nothing 0))
  loop [W64] [W 0] $ \again, [i] =>
    branch EqR i n
      (do mapped <- emit1 (Arith Add bytes (W (cast allocationMargin)))
          w <- emit1 (SystemCall 6 [W 9, W 0, mapped, W 3, W 0x22, W (-1), W 0])
          base <- emit1 (WordToByteAddr w)
          hp <- emit1 (Offset base bytes)
          emit0 (SetPinned Hp hp)
          emit0 (SetPinned HpLim hp)
          ret [w]) $ do
      off <- emit1 (Arith Shl i (W 3))
      at <- emit1 (Offset roots off)
      v <- emit1 (Load W64 (MkMem (AtBytes at) Nothing 0))
      tag <- emit1 (Arith And v (W 1))
      -- a fixnum stays; an object moves
      branch NeR tag (W 0) (do i' <- emit1 (Arith Add i (W 1)); again [i']) $ do
        old <- emit1 (WordToByteAddr v)
        c <- emit1 (SystemCall 6 [W 9, W 0, W 16, W 3, W 0x22, W (-1), W 0])
        copy <- emit1 (WordToByteAddr c)
        h <- emit1 (Load W64 (MkMem (AtBytes old) Nothing 0))
        f <- emit1 (Load W64 (MkMem (AtBytes old) Nothing 8))
        emit0 (Store W64 (MkMem (AtBytes copy) Nothing 0) h)
        emit0 (Store W64 (MkMem (AtBytes copy) Nothing 8) f)
        emit0 (Store W64 (MkMem (AtBytes old) Nothing 8) (W 199))
        emit0 (Store W64 (MkMem (AtBytes at) Nothing 0) c)
        i' <- emit1 (Arith Add i (W 1))
        again [i']

||| The runtime's `allocMutable`: the slow path's body.
allocMutableBody : Closed T (Direct [W64] False) False [W64]
allocMutableBody = build $ \[bytes] => do
  w <- emit1 (SystemCall 6 [W 9, W 0, bytes, W 3, W 0x22, W (-1), W 0])
  base <- emit1 (WordToByteAddr w)
  hp <- emit1 (Offset base bytes)
  emit0 (SetPinned Hp hp)
  emit0 (SetPinned HpLim hp)
  ret [w]

||| The runtime's `crash`: the message to the standard error, status 1.
crashBody : Closed T (Direct [] False) False [W64, W64]
crashBody = build $ \[message, length] => do
  _ <- emit1 (SystemCall 6 [W 1, W 2, message, length, W 0, W 0, W 0])
  _ <- emit1 (SystemCall 6 [W 231, W 1, W 0, W 0, W 0, W 0, W 0])
  ret []

mainClosed : Maybe (Body T CPS False [] [])
mainClosed = close mainBody

keepClosed : Maybe (Body T CPS False [] [Val])
keepClosed = close keepBody

crashClosed, startClosed : Maybe (Body T (Direct [] False) False [] [W64, W64])
crashClosed = close crashBody
startClosed = close startBody

allocSlowClosed, allocMutableClosed : Maybe (Body T (Direct [W64] False) False [] [W64])
allocSlowClosed = close allocSlowBody
allocMutableClosed = close allocMutableBody

||| The term program, its bodies closed, its names distinct.
term : Maybe (TermIR.Program.Program TestEnc T)
term = do
  Left ok <- Just (choose (distinct (map (.name) (sigs T)) && distinct (map (.sym) (statics T))))
    | Right _ => Nothing
  m <- mainClosed
  k <- keepClosed
  cr <- crashClosed
  st <- startClosed
  al <- allocSlowClosed
  am <- allocMutableClosed
  pure (MkProgram {d = T} [Defined m, Defined k, Defined cr, Defined st, Defined al, Defined am]
          [] (MkEntry here) noConIds)

||| The program allocated as the code generator allocates it.
allocated : TermIR.Program.Program TestEnc T -> LocatedIR.Program.Program TestEnc
allocated t =
  let called = callClobbers x86_64 in
  localAssign (row called) (termRow called) cycleTemp (allocRegs x86_64 t)

0 Steps : Type
Steps = List (LocatedIR.Step.Step TestEnc)

||| The steps with slot `n` held in register `r` of its class from the step
||| that writes it: a move into the register after that step, and every
||| later read of the slot, and its place in a live list, of the register.
hold : (n, r : Nat) -> Steps -> Steps
hold n r ss = case break writes ss of
  (before, w :: after) => case into w of
    Just m => before ++ w :: m :: map renamed after
    Nothing => ss
  _ => ss
  where
    isSlot : Place TestEnc -> Bool
    isSlot (At (Slot m _)) = m == n
    isSlot _ = False

    writes : LocatedIR.Step.Step TestEnc -> Bool
    writes st = any isSlot (results st)

    -- the move of the slot into the register, at the slot's type
    into : LocatedIR.Step.Step TestEnc -> Maybe (LocatedIR.Step.Step TestEnc)
    into st = case filter isSlot (results st) of
      (At (Slot m t) :: _) => Just (Move (Register r t) (Slot m t))
      _ => Nothing

    rename : Location.Step () TestEnc
    rename () l@(Slot m t) = ((), if m == n then Register r t else l)
    rename () l = ((), l)

    place : Place TestEnc -> Place TestEnc
    place (At l) = At (snd (rename () l))

    renamed : LocatedIR.Step.Step TestEnc -> LocatedIR.Step.Step TestEnc
    renamed st = case snd (traverseOperands rename () st) of
      Op d (LocatedIR.Instr.AllocObj o h fs live) =>
        Op d (LocatedIR.Instr.AllocObj o h fs (map place live))
      st' => st'

||| `keep`'s values in registers across its allocations: its 7 words in
||| rsi, rdi, r8 to r11 and r13, its double in xmm3, its object in rbp,
||| each from where it is made; and the stand-in `allocSlow`'s first three
||| values, its junk, in r13, rbp and xmm3 (`junked`).
inRegisters : LocatedIR.Program.Program TestEnc -> LocatedIR.Program.Program TestEnc
inRegisters p = { functions $= map fn } p
  where
    holds, junked : Steps -> Steps
    holds = hold 9 10 . hold 8 3 . hold 7 9 . hold 6 8 . hold 5 7 . hold 4 6 . hold 3 5 . hold 2 4
              . hold 1 3
    junked = hold 3 3 . hold 2 10 . hold 1 9

    entry : (Steps -> Steps) -> Block TestEnc -> Block TestEnc
    entry f (MkBlock 0 ps cert body t n) = MkBlock 0 ps cert (f body) t n
    entry _ b = b

    fn : Function TestEnc -> Function TestEnc
    fn g = if g.name == nm "keep" then { blocks $= map (entry holds) } g
           else if g.name == flatName runtimeAllocSlow then { blocks $= map (entry junked) } g
           else g

||| A table's width by the routine its stub calls.
calledWidth : Asm.Instr -> Maybe SubWord
calledWidth (Call l) =
  find (\w => label (SymAllocLive w) == l || label (SymAllocSized w) == l) [Sub8, Sub16, Sub32]
calledWidth _ = Nothing

||| The tables of a function's code: the words each lists, and whether it
||| has the floating-point registers saved.
tables : List Asm.Instr -> List String
tables (c :: Jmp _ :: Bytes bs :: is) = case calledWidth c of
  Just w => describe w bs :: tables is
  Nothing => tables is
  where
    describe : SubWord -> List Bits8 -> String
    describe w bs = case tableEntries w bs of
      Just (floats, words) =>
        "  GC-visible words " ++ show words
          ++ (if floats then ", the floating-point registers saved" else "")
      Nothing => "  not a table"
tables (_ :: is) = tables is
tables [] = []

||| A function's name, from the comment its code starts with.
named : List Asm.Instr -> String
named (Comment s :: _) = s
named _ = "?"

covering
main : IO ()
main = do
  let Just t = term | Nothing => putStrLn "a level outside its context, or names repeat"
  let run = inRegisters (allocated t)
      called = callClobbers x86_64
  -- the value check holds the program to the term: registers survive an
  -- allocation of a fixed size, the GC-visible ones listed
  putStrLn ("the value check: "
            ++ either id (const "accepted") (check (clobbers called) (termClobbers called) t run))
  let Right renderer = render TestEnc realised run
    | Left err => putStrLn ("render: " ++ err)
  -- an 8-byte window: every allocation takes the slow path
  asm <- seeded TestEnc 8 renderer.labelsBefore
  seen <- newIORef [<]
  Right rendered <- renderInto asm (\is => modifyIORef seen (:< is)) renderer
    | Left err => putStrLn ("render: " ++ err)
  fs <- readIORef seen
  traverse_ (\is => when (named is == "Main.keep") $ do
                       putStrLn "Main.keep:"
                       traverse_ putStrLn (tables is))
            (fs <>> [])
  Right image <- linked rendered.areas asm rendered.rodata
    | Left problems => putStrLn ("link: " ++ show problems)
  Right () <- writeImage "keep" image
    | Left err => putStrLn ("write: " ++ show err)
  pure ()
