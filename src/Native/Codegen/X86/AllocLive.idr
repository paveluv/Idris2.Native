||| The slow paths the allocation sites of generated code share, on x86-64,
||| and the cold code of a site that calls one (`stub`).
|||
||| A site of a fixed size, up to the allocation margin (`Instr.withinMargin`),
||| checks the allocation pointer against the limit before it bumps it;
||| past the limit it jumps to its cold code: a call of the routine for
||| its table's width (`idris_alloc_live8`, `16`, `32`), a jump back to the
||| bump, and the site's live table (`Native.LiveTable`), which nothing
||| executes. The routine (`routine`) keeps every register: it saves each
||| allocatable one in `SAVE` (the floating-point ones only where the table
||| says), puts the GC-visible words the table lists in `ROOTS`, above the
||| entries in use, with `NROOTS` raised once every one is written, so that
||| the collector forwards them, and calls `idris_alloc_slow` for no bytes:
||| a collection if one is due, then a window at the allocation pointer.
||| It reloads the listed words as the collector left them, restores the
||| registers from `SAVE`, the GC-visible ones forwarded, and returns to
||| the stub's jump back to the bump, which the window's margin past the
||| limit holds.
|||
||| A site whose size is known only at run time, or one past the margin,
||| bumps first, then checks; past the limit its cold code calls the sized
||| routine (`sizedRoutine`, `idris_alloc_sized8`, `16`, `32`), which takes
||| the bytes as the bump left them, roots the slots the table lists, calls
||| `idris_alloc_slow` for them, and returns to the stub's jump past the
||| check with rax the object's room. It keeps no register: such a site's
||| row says so.
|||
||| A live table's entry is a word of `SAVE`'s word registers and of
||| `SCRATCH` after them (`savedWord`, `slotWord`). Neither routine touches
||| a raw slot: nothing `idris_alloc_slow` runs writes `SCRATCH`, the
||| runtime being Direct code, whose slots are in frames of its own.
module Native.Codegen.X86.AllocLive

import Native.Codegen.X86.AccessWidth
import Native.Codegen.X86.Asm
import Native.Codegen.X86.Encode
import Native.Codegen.X86.RegSet
import Native.Codegen.X86.Target

import Native.Area
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Codegen.Linkage.Sym as Linkage
import Native.Codegen.LocatedIR.Location as LocatedIR
import Native.Codegen.RegDesc
import Native.Codegen.Target
import Native.Data.Numbered as Data
import Native.LiveTable
import Native.Rep
import Native.Types.Enc as Types
import Native.Width

%default total

||| The allocatable registers, in the order of the target's description.
words : List Asm.Reg64
words = map Asm.regOfNum Target.x86_64.allocatable.words

floats : List Asm.Xmm
floats = map Asm.xmmOfNum Target.x86_64.allocatable.floats

||| The words of `SAVE`: one for each allocatable word register, in the order
||| of the target's description; `SCRATCH` follows.
export
saveWords : Nat
saveWords = length words

||| The words of `FSAVE`: one for each allocatable floating-point register,
||| in the order of the target's description.
export
floatSaveWords : Nat
floatSaveWords = length floats

||| A word register's word, as a live table's entry: its index in the
||| target's description.
export
savedWord : (index : Nat) -> Nat
savedWord i = i

||| A slot's word, as a live table's entry: past the word registers'.
export
slotWord : (slot : Nat) -> Nat
slotWord n = length words + n

||| Whether the fixed-size slow path is to save the floating-point registers
||| for a site of the live list: where a value is live in one.
export
savesFloats : List (LocatedIR.Location.Place enc) -> Bool
savesFloats = any isFloat
  where
    isFloat : LocatedIR.Location.Place enc -> Bool
    isFloat (LocatedIR.Location.At (LocatedIR.Location.Register _ t)) =
      IRCommon.Ty.class t == Rep.FloatClass
    isFloat _ = False

||| Where a stub's table starts, in bytes from the address its call returns
||| to: past the jump back, whose length never changes.
export
tableAt : Int
tableAt = Encode.instrSize 0 (Asm.Jmp 0)

||| A site's cold code: the call of the routine, the jump back to the site's
||| code at `back`, and the table's bytes.
export
stub : (routine : Linkage.Sym) -> (back : Asm.Label) -> (Width.SubWord, List Bits8) ->
       List Asm.Instr
stub r back (w, bytes) =
  [ Asm.Call (Linkage.Sym.label r)
  , Asm.Jmp back
  , Asm.Bytes bytes ]

||| What the fixed-size routine may leave changed: r12, the continuation,
||| which the collector may move; r14 and r15, the window; and the
||| floating-point registers, which it restores only where the table says. The
||| words it saves and restores it leaves as they were, or as the collector
||| forwarded them. The rendering checks it against what the routine and every
||| function `idris_alloc_slow` reaches write, the registers it restores aside
||| (`Clobbers.restored`).
export
clobbers : RegSet
clobbers =
  RegSet.union (RegSet.gprs [Asm.R12, Asm.R14, Asm.R15])
    (foldl (\s, x => RegSet.union s (RegSet.xmm x)) RegSet.none floats)

||| What the sized routine may leave changed: every allocatable register,
||| rax the object's room among them, since it keeps none; r12; r14 and r15.
export
sizedClobbers : RegSet
sizedClobbers = foldl (\s, r => RegSet.union s (RegSet.gpr r)) clobbers words

||| The labels a fixed-size routine takes for itself.
export
routineLabels : Nat
routineLabels = 6

||| The labels a sized routine takes for itself.
export
sizedRoutineLabels : Nat
sizedRoutineLabels = 4

area : Linkage.Sym -> Int -> Asm.Mem
area s off = Asm.MRip (Linkage.Sym.label s) off

||| The word of `SAVE` of the word register at the index.
wordSave : Nat -> Asm.Mem
wordSave i = area Linkage.Sym.SymSave (cast (8 * i))

||| The table's count, by rsi, its address.
count : Width.SubWord -> Asm.Mem
count w = Asm.MBase Asm.RSI (cast (LiveTable.countAt w))

||| A number of the table into the register.
entry : Width.SubWord -> Asm.Reg64 -> Asm.Mem -> Asm.Instr
entry w r = Asm.Load (AccessWidth.accessWidth w) False r

||| For each of the rcx words whose entries start at rdx: the word's
||| address in r11, from rax, the first word register's word, then `move`
||| between the word and the root at r9, which moves on to the next root
||| each time.
walk : Width.SubWord -> Asm.Label -> (move : List Asm.Instr) -> List Asm.Instr
walk w l move =
  [ Asm.Lbl l
  , entry w Asm.R11 (Asm.MBase Asm.RDX 0)
  , Asm.ShiftI Asm.SHL Asm.R11 3
  , Asm.Alu Asm.ADD Asm.R11 Asm.RAX ]
  ++ move ++
  [ Asm.AluI Asm.ADD Asm.R9 (cast (Area.rootOffset 1))
  , Asm.AluI Asm.ADD Asm.RDX (cast (Width.subWordBytes w))
  , Asm.AluI Asm.SUB Asm.RCX 1
  , Asm.Jcc Asm.NE l ]

save, reload : List Asm.Instr
save =
  [ Asm.MovRM Asm.R11 (Asm.MBase Asm.R11 0)
  , Asm.MovMR (Asm.MBase Asm.R9 0) Asm.R11 ]
reload =
  [ Asm.MovRM Asm.R8 (Asm.MBase Asm.R9 0)
  , Asm.MovMR (Asm.MBase Asm.R11 0) Asm.R8 ]

||| The table's words onto `ROOTS` from entry n, `NROOTS` then raised to n
||| plus their number: rsi the table, rcx its count, halved.
rooting : Width.SubWord -> (roots, rooted : Asm.Label) -> List Asm.Instr
rooting w roots rooted =
  [ Asm.Lea Asm.RAX (wordSave 0)
  , Asm.Lea Asm.R10 (area Linkage.Sym.SymNRoots 0)
  , Asm.MovRM Asm.R8 (Asm.MBase Asm.R10 0)
  , Asm.MovRR Asm.R9 Asm.R8
  , Asm.ShiftI Asm.SHL Asm.R9 (cast Area.rootShift)
  , Asm.Lea Asm.RDX (area Linkage.Sym.SymRoots 0)
  , Asm.Alu Asm.ADD Asm.R9 Asm.RDX
  , Asm.Alu Asm.ADD Asm.R8 Asm.RCX
  , Asm.Lea Asm.RDX (Asm.MBase Asm.RSI (cast (LiveTable.entriesAt w)))
  , Asm.Test Asm.RCX Asm.RCX
  , Asm.Jcc Asm.E rooted ]
  ++ walk w roots save ++
  [ Asm.Lbl rooted
  , Asm.MovMR (Asm.MBase Asm.R10 0) Asm.R8 ]

||| `NROOTS` back to n, and the table's words reloaded from there: rsi the
||| table, rcx its count, halved.
unrooting : Width.SubWord -> (unroots, unrooted : Asm.Label) -> List Asm.Instr
unrooting w unroots unrooted =
  [ Asm.Lea Asm.RAX (wordSave 0)
  , Asm.Lea Asm.R10 (area Linkage.Sym.SymNRoots 0)
  , Asm.MovRM Asm.R8 (Asm.MBase Asm.R10 0)
  , Asm.Alu Asm.SUB Asm.R8 Asm.RCX
  , Asm.MovMR (Asm.MBase Asm.R10 0) Asm.R8
  , Asm.ShiftI Asm.SHL Asm.R8 (cast Area.rootShift)
  , Asm.Lea Asm.R9 (area Linkage.Sym.SymRoots 0)
  , Asm.Alu Asm.ADD Asm.R9 Asm.R8
  , Asm.Lea Asm.RDX (Asm.MBase Asm.RSI (cast (LiveTable.entriesAt w)))
  , Asm.Test Asm.RCX Asm.RCX
  , Asm.Jcc Asm.E unrooted ]
  ++ walk w unroots reload ++
  [ Asm.Lbl unrooted ]

||| The fixed-size routine for tables of the width, its own labels numbered
||| from `first`, `routineLabels` of them.
|||
||| Entered by a stub's call, before the site's bump: r15 the allocation
||| pointer, at or past the limit, r12 a complete continuation, and the
||| stack pointer 8 below a multiple of 16, the call having pushed a word.
||| The frame is one word, the table's address, so that the stack is
||| 16-aligned at the call of `idris_alloc_slow`. Leaves every register it
||| saved as it was, or as the collector forwarded it where the table lists
||| it, r15 and r14 the window `idris_alloc_slow` opened, rbx as it was, r12
||| as the collector left it, and `NROOTS` and the stack as they were.
export
routine : Width.SubWord -> (first : Asm.Label) -> List Asm.Instr
routine w first =
  [ Asm.Align 16
  , Asm.Lbl (Linkage.Sym.label (Linkage.Sym.SymAllocLive w)) ]
  -- every word register in its word
  ++ map (\(i, r) => Asm.MovMR (wordSave i) r) (Data.Numbered.numbered words) ++
  -- the table, and the floating-point registers in theirs where it says
  [ Asm.MovRM Asm.RSI (Asm.MBase Asm.RSP 0)
  , Asm.AluI Asm.ADD Asm.RSI tableAt
  , entry w Asm.RCX (count w)
  , Asm.TestI Asm.RCX 1
  , Asm.Jcc Asm.E floatsSaved ]
  ++ map (\(i, x) => Asm.MovsdMR (floatSave i) x) (Data.Numbered.numbered floats) ++
  [ Asm.Lbl floatsSaved
  , Asm.ShiftI Asm.SHR Asm.RCX 1 ]
  ++ rooting w roots rooted ++
  -- room only, at the allocation pointer: the site's bump makes the object
  [ Asm.Push Asm.RSI
  , Asm.Alu Asm.XOR Asm.RDI Asm.RDI
  , Asm.Call (Linkage.Sym.label Linkage.Sym.SymAllocSlow)
  , Asm.Pop Asm.RSI
  , entry w Asm.RCX (count w)
  , Asm.ShiftI Asm.SHR Asm.RCX 1 ]
  ++ unrooting w unroots unrooted ++
  [ entry w Asm.RCX (count w)
  , Asm.TestI Asm.RCX 1
  , Asm.Jcc Asm.E floatsRestored ]
  ++ map (\(i, x) => Asm.MovsdRM x (floatSave i)) (Data.Numbered.numbered floats) ++
  [ Asm.Lbl floatsRestored ]
  -- every word register from its word, the GC-visible ones as forwarded
  ++ map (\(i, r) => Asm.MovRM r (wordSave i)) (Data.Numbered.numbered words) ++
  [ Asm.Ret ]
  where
    floatsSaved, floatsRestored, roots, rooted, unroots, unrooted : Asm.Label
    floatsSaved = first
    floatsRestored = first + 1
    roots = first + 2
    rooted = first + 3
    unroots = first + 4
    unrooted = first + 5

    ||| The word of `SAVE` of the floating-point register at the index.
    floatSave : Nat -> Asm.Mem
    floatSave i = area Linkage.Sym.SymFSave (cast (8 * i))

||| The sized routine for tables of the width, its own labels numbered from
||| `first`, `sizedRoutineLabels` of them.
|||
||| Entered by a stub's call, after the site's bump: rax the object, r15
||| past it by its bytes, r12 a complete continuation, and the stack
||| pointer 8 below a multiple of 16. The frame is one word, the table's
||| address. Leaves rax the object's room, r15 and r14 the window
||| `idris_alloc_slow` left, rbx as it was, r12 and every slot the table
||| lists as they were or as the collector forwarded them, and `NROOTS` and
||| the stack as they were. Keeps no other register (`sizedClobbers`).
export
sizedRoutine : Width.SubWord -> (first : Asm.Label) -> List Asm.Instr
sizedRoutine w first =
  [ Asm.Align 16
  , Asm.Lbl (Linkage.Sym.label (Linkage.Sym.SymAllocSized w))
  -- the bytes, as `idris_alloc_slow` takes them, and the window as the
  -- fast path found it
  , Asm.MovRR Asm.RDI Asm.R15
  , Asm.Alu Asm.SUB Asm.RDI Asm.RAX
  , Asm.MovRR Asm.R15 Asm.RAX
  -- the table
  , Asm.MovRM Asm.RSI (Asm.MBase Asm.RSP 0)
  , Asm.AluI Asm.ADD Asm.RSI tableAt
  , entry w Asm.RCX (count w)
  , Asm.ShiftI Asm.SHR Asm.RCX 1 ]
  ++ rooting w roots rooted ++
  [ Asm.Push Asm.RSI
  , Asm.Call (Linkage.Sym.label Linkage.Sym.SymAllocSlow)
  , Asm.Pop Asm.RSI
  , entry w Asm.RCX (count w)
  , Asm.ShiftI Asm.SHR Asm.RCX 1 ]
  ++ unrooting w unroots unrooted ++
  -- the object's room, which the unrooting leaves in rdi
  [ Asm.MovRR Asm.RAX Asm.RDI
  , Asm.Ret ]
  where
    roots, rooted, unroots, unrooted : Asm.Label
    roots = first
    rooted = first + 1
    unroots = first + 2
    unrooted = first + 3
