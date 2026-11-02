-- The slow path every allocation site shares, run on live tables that
-- ordinary programs seldom or never make: a slot past 65,535, which needs
-- the table's widest entries; raw slots live, two and three at once, which
-- the table does not list; nothing live at all.
--
-- A function's registers are slots of SCRATCH, one for each value it binds,
-- so a function that binds 65,537 values has slots past 65,535; an Idris
-- function that long is no test anyone would write, but the term IR builds
-- one in a loop. A raw value is a machine word or a double, which the
-- collector must never see: the slow path leaves those in their slots,
-- which nothing it runs writes, and puts the GC-visible ones in ROOTS. In
-- ordinary code a raw value is live across an allocation mostly while it is
-- boxed, one at a time.
--
-- Each allocation here takes the slow path: the allocation window is 8
-- bytes, and the program's own `allocSlow` leaves it empty. That
-- `allocSlow` overwrites the GC-visible slots of SCRATCH the tables list,
-- so a slot the shared slow path does not restore from ROOTS comes back
-- with `allocSlow`'s word, and the check after the allocation fails; it
-- leaves the raw ones, as the runtime's does, and the checks after show
-- them kept. It collects nothing: what a collection does to the saved
-- values is native/alloc002's.
--
-- The program prints each function's tables, as the code generator wrote
-- them, and exits with 0 when every check passes.
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
import Native.Codegen.LocatedIR.Program
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

||| The values `deep` binds: one more than slot 65,535 needs.
deepValues : Nat
deepValues = 65537

||| The GC-visible slots of SCRATCH the tables list that `allocSlow`
||| overwrites: slot 0, `main`'s, `deep`'s and `raws`' first value, and
||| `deep`'s fixnum, after its 65,537 words. `deep`'s pair, after it, it
||| leaves alone: a wrong word there would be a fault, not a failed check.
overwritten : List Nat
overwritten = [0, deepValues + 2]

T : Decls TestEnc
T = MkDecls
  [ MkSig (nm "main") CPS [] False
  , MkSig (nm "deep") CPS [Val] False
  , MkSig (nm "raws") CPS [Val] False
  , MkSig (flatName runtimeCrash) (Direct [] False) [W64, W64] False
  , MkSig (flatName runtimeStart) (Direct [] False) [W64, W64] False
  , MkSig (flatName runtimeAllocSlow) (Direct [W64] False) [W64] False
  , MkSig (flatName runtimeAllocMutable) (Direct [W64] False) [W64] False ]
  []

deepRef : Var (sigs T) (MkSig (nm "deep") CPS [Val] False)
deepRef = later here

rawsRef : Var (sigs T) (MkSig (nm "raws") CPS [Val] False)
rawsRef = later (later here)

||| `n` values, each one more than the one before, from `x`: the last.
count : Nat -> Opnd vr W64 -> Build T c False vr l (Opnd vr W64)
count Z x = pure x
count (S n) x = do
  y <- emit1 (Arith Add x (W 1))
  count n y

||| A fixnum's word.
untagged : Opnd vr Val -> Build T c False vr l (Opnd vr W64)
untagged v = do
  f <- emit1 (NarrowFix v)
  emit1 (Untag f)

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
||| after overwriting the callers' GC-visible slots, which the shared slow
||| path restores from ROOTS: `bytes` fresh from the system, the object at
||| their start, and the window left empty, so that the next allocation
||| comes here too. Nothing is collected.
allocSlowBody : Closed T (Direct [W64] False) False [W64]
allocSlowBody = build $ \[bytes] => do
  scratch <- emit1 (AreaAddr SCRATCH)
  -- each overwritten slot i set to i + bytes
  traverse_ (\i => do v <- emit1 (Arith Add (W (cast i)) bytes)
                      emit0 (Store W64 (MkMem (AtBytes scratch) (Just (W (cast i))) 0) v))
    overwritten
  w <- emit1 (SystemCall 6 [W 9, W 0, bytes, W 3, W 0x22, W (-1), W 0])
  base <- emit1 (WordToByteAddr w)
  hp <- emit1 (Offset base bytes)
  emit0 (SetPinned Hp hp)
  emit0 (SetPinned HpLim hp)
  ret [w]

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

||| Values in slots past 65,535 live across two allocations, as
|||
|||   deep x = let w = 65537
|||                o = MkPair x (fixnum w)    -- x, the fixnum and w live
|||                s = a string of 8 bytes    -- o and w live
|||            in if w, o's fields and their order are as made then 0 else crash
|||
||| where `w` is the last of 65,537 values counted up from 0, each in a slot
||| of its own: a raw word in a slot past 65,535, and its fixnum in the
||| next, GC-visible.
deepBody : Closed T CPS False [Val]
deepBody = build $ \[x] => do
  w <- count deepValues (W 0)
  f <- emit1 (Tag w)
  v <- emit1 (WidenFix f)
  o <- emit1 (AllocObj (ConH 0 2) [x, v])
  leaveIf NeR w (W 65537) (crash "deep: the raw slot past 65,535 not kept")
  _ <- emit1 (AllocSized StringBytesP (W 8) ())
  leaveIf NeR w (W 65537) (crash "deep: the raw slot not kept after the string")
  a <- emit1 (Load Val (MkMem (AtPtr o) Nothing 8))
  b <- emit1 (Load Val (MkMem (AtPtr o) Nothing 16))
  aw <- untagged a
  bw <- untagged b
  leaveIf NeR aw (W 7) (crash "deep: the parameter's slot not restored")
  leaveIf NeR bw (W 65537) (crash "deep: the GC-visible slot past 65,535 not restored")
  return (Vx {enc = TestEnc} 0)

||| Three raw words live across an allocation, then two, then nothing, as
|||
|||   raws x = let a = x + 10; b = x + 20; c = x + 30
|||                _ = Box x        -- x, and a, b and c, raw
|||                _ = Box x        -- x, and a and b
|||                _ = Box 0        -- nothing
|||            in if a, b and c are as made then 0 else crash
rawsBody : Closed T CPS False [Val]
rawsBody = build $ \[x] => do
  xw <- untagged x
  a <- emit1 (Arith Add xw (W 10))
  b <- emit1 (Arith Add xw (W 20))
  c <- emit1 (Arith Add xw (W 30))
  _ <- emit1 (AllocObj (ConH 0 1) [x])
  leaveIf NeR c (W 37) (crash "raws: the third raw slot not kept")
  _ <- emit1 (AllocObj (ConH 0 1) [x])
  leaveIf NeR a (W 17) (crash "raws: the first raw slot not kept")
  leaveIf NeR b (W 27) (crash "raws: the second raw slot not kept")
  _ <- emit1 (AllocObj (ConH 0 1) [Vx {enc = TestEnc} 0])
  return (Vx {enc = TestEnc} 0)

||| `deep 7` and `raws 7`, each a call whose continuation is allocated
||| through the slow path too; the status 0 when both give 0.
mainBody : Closed T CPS False []
mainBody = build $ \[] => do
  d <- call deepRef [Vx {enc = TestEnc} 7]
  r <- call rawsRef [Vx {enc = TestEnc} 7]
  dw <- untagged d
  rw <- untagged r
  leaveIf NeR dw (W 0) (crash "deep: not 0")
  leaveIf NeR rw (W 0) (crash "raws: not 0")
  return (Vx {enc = TestEnc} 0)

||| A table's width by the routine its stub calls.
calledWidth : Asm.Instr -> Maybe SubWord
calledWidth (Call l) =
  find (\w => label (SymAllocLive w) == l) [Sub8, Sub16, Sub32]
calledWidth _ = Nothing

||| The tables of a function's code: the width of each, by the call before
||| it, and its counts.
tables : List Asm.Instr -> List String
tables (c :: Jmp _ :: Bytes bs :: is) = case calledWidth c of
  Just w => describe w bs :: tables is
  Nothing => tables is
  where
    describe : SubWord -> List Bits8 -> String
    describe w bs = case tableSlots w bs of
      Just slots => "  " ++ show (8 * subWordBytes w) ++ "-bit, GC-visible slots " ++ show slots
      Nothing => "  not a table"
tables (_ :: is) = tables is
tables [] = []

||| A function's name, from the comment its code starts with.
named : List Asm.Instr -> String
named (Comment s :: _) = s
named _ = "?"

-- Each body closed in a definition of its own type: closed one after
-- another in `main`'s lets, the closings' metavariables would make
-- elaboration take exponential time.
mainClosed : Maybe (Body T CPS False [] [])
mainClosed = close mainBody

deepClosed, rawsClosed : Maybe (Body T CPS False [] [Val])
deepClosed = close deepBody
rawsClosed = close rawsBody

crashClosed, startClosed : Maybe (Body T (Direct [] False) False [] [W64, W64])
crashClosed = close crashBody
startClosed = close startBody

allocSlowClosed, allocMutableClosed : Maybe (Body T (Direct [W64] False) False [] [W64])
allocSlowClosed = close allocSlowBody
allocMutableClosed = close allocMutableBody

||| The program, its bodies closed, its names distinct.
program : Maybe (LocatedIR.Program.Program TestEnc)
program = do
  Left ok <- Just (choose (distinct (map (.name) (sigs T)) && distinct (map (.sym) (statics T))))
    | Right _ => Nothing
  m <- mainClosed
  d <- deepClosed
  r <- rawsClosed
  cr <- crashClosed
  st <- startClosed
  al <- allocSlowClosed
  am <- allocMutableClosed
  -- allocated as the code generator allocates: a slot for every value,
  -- then each instruction's operands moved into the registers its
  -- rendering reads them in, and its results out of them
  let called = callClobbers x86_64
  pure
    (localAssign (row called) (termRow called) cycleTemp $ allocRegs x86_64
      (MkProgram {d = T}
        [Defined m, Defined d, Defined r, Defined cr, Defined st, Defined al, Defined am]
        [] (MkEntry here) noConIds))

covering
main : IO ()
main = do
  let Just run = program | Nothing => putStrLn "a level outside its context, or names repeat"
  let Right renderer = render TestEnc realised run
    | Left err => putStrLn ("render: " ++ err)
  -- an 8-byte window: the first allocation takes the slow path
  asm <- seeded TestEnc 8 renderer.labelsBefore
  seen <- newIORef [<]
  Right rendered <- renderInto asm (\is => modifyIORef seen (:< is)) renderer
    | Left err => putStrLn ("render: " ++ err)
  fs <- readIORef seen
  traverse_ (\is => case tables is of
                      [] => pure ()
                      ts => do putStrLn (named is ++ ":"); traverse_ putStrLn ts)
            (fs <>> [])
  Right image <- linked rendered.areas asm rendered.rodata
    | Left problems => putStrLn ("link: " ++ show problems)
  Right () <- writeImage "term" image
    | Left err => putStrLn ("write: " ++ show err)
  pure ()
