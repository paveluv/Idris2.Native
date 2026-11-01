||| The slow path every allocation site of generated code shares, on x86-64
||| (`idris_alloc_live8`, `16`, `32`), and the cold code of a site that calls
||| it (`stub`).
|||
||| A site's fast path bumps r15 by the object's bytes, then checks it
||| against r14; past the limit it jumps to its cold code: a call of the
||| routine for its table's width, a jump back to the site, and the site's
||| live table (`Native.LiveTable`), which nothing executes. The routine
||| finds the table after the jump its call returns to. It roots what the
||| table lists across `idris_alloc_slow`: the GC-visible slots in `ROOTS`,
||| above the entries in use, with `NROOTS` raised once every one is
||| written, so that the collector forwards them; the raw ones in a frame of
||| its own on the machine stack, which the collector never reads. It
||| reloads them all after the call, the GC-visible ones as the collector
||| left them, and returns to the stub's jump with rax the object's room.
module Native.Codegen.X86.AllocLive

import Native.Codegen.X86.AccessWidth
import Native.Codegen.X86.Asm
import Native.Codegen.X86.Encode
import Native.Codegen.X86.RegSet

import Native.Area
import Native.Codegen.Linkage.Sym as Linkage
import Native.LiveTable
import Native.Width

%default total

||| Where a stub's table starts, in bytes from the address its call returns
||| to: past the jump back, whose length never changes.
export
tableAt : Int
tableAt = Encode.instrSize 0 (Asm.Jmp 0)

||| A site's cold code: the call of the routine for the table's width, the
||| jump back to the site's code at `done`, and the table's bytes.
export
stub : (done : Asm.Label) -> (Width.SubWord, List Bits8) -> List Asm.Instr
stub done (w, bytes) =
  [ Asm.Call (Linkage.Sym.label (Linkage.Sym.SymAllocLive w))
  , Asm.Jmp done
  , Asm.Bytes bytes ]

||| What the routine may leave changed: rax, the object's room; rbx,
||| `SCRATCH`; r12, the continuation, which the collector may move; r14 and
||| r15, the window; and rcx, rdx, rsi, rdi and r8 to r11, which it and
||| `idris_alloc_slow` use. The rendering checks it against what the routine
||| and every function `idris_alloc_slow` reaches write (`Clobbers`).
export
clobbers : RegSet
clobbers =
  RegSet.gprs [ Asm.RAX, Asm.RCX, Asm.RDX, Asm.RBX, Asm.RSI, Asm.RDI, Asm.R8, Asm.R9, Asm.R10
              , Asm.R11, Asm.R12, Asm.R14, Asm.R15 ]

||| The labels a routine takes for itself.
export
routineLabels : Nat
routineLabels = 8

||| The routine for tables of the width, its own labels numbered from
||| `first`, `routineLabels` of them.
|||
||| Entered by a stub's call: rax is the object, r15 past it by its bytes,
||| r12 a complete continuation, and the stack pointer 8 below a multiple of
||| 16, the call having pushed a word. The frame is an odd number of words,
||| the table's address and the raw slots, so that the stack is 16-aligned
||| at the call of `idris_alloc_slow`. Leaves rax the object's room, r15 and
||| r14 the window `idris_alloc_slow` left, rbx `SCRATCH`, r12 and every
||| slot the table lists as they were or as the collector forwarded them,
||| and `NROOTS` and the stack as they were. Clobbers rcx, rdx, rsi, rdi, r8
||| to r11 and the flags (`clobbers`).
export
routine : Width.SubWord -> (first : Asm.Label) -> List Asm.Instr
routine w first =
  [ Asm.Align 16
  , Asm.Lbl (Linkage.Sym.label (Linkage.Sym.SymAllocLive w))
  -- the bytes, as `idris_alloc_slow` takes them, and the window as the
  -- fast path found it
  , Asm.MovRR Asm.RDI Asm.R15
  , Asm.Alu Asm.SUB Asm.RDI Asm.RAX
  , Asm.MovRR Asm.R15 Asm.RAX
  , Asm.Lea Asm.RBX (area Linkage.Sym.SymScratch)
  -- the table
  , Asm.MovRM Asm.RSI (Asm.MBase Asm.RSP 0)
  , Asm.AluI Asm.ADD Asm.RSI tableAt
  -- the GC-visible slots onto ROOTS from entry n, then NROOTS raised to n + g
  , Asm.Lea Asm.R10 (area Linkage.Sym.SymNRoots)
  , Asm.MovRM Asm.R8 (Asm.MBase Asm.R10 0)
  , Asm.MovRR Asm.R9 Asm.R8
  , Asm.ShiftI Asm.SHL Asm.R9 (cast Area.rootShift)
  , Asm.Lea Asm.RDX (area Linkage.Sym.SymRoots)
  , Asm.Alu Asm.ADD Asm.R9 Asm.RDX
  , entry Asm.RCX gcCount
  , Asm.Alu Asm.ADD Asm.R8 Asm.RCX
  , Asm.Lea Asm.RDX (Asm.MBase Asm.RSI (cast (LiveTable.slotsAt w)))
  , Asm.Test Asm.RCX Asm.RCX
  , Asm.Jcc Asm.E rooted ]
  ++ walk roots rootBytes save ++
  [ Asm.Lbl rooted
  , Asm.MovMR (Asm.MBase Asm.R10 0) Asm.R8
  -- the frame: the table's address, then the raw slots
  , entry Asm.RCX rawCount
  , Asm.Lea Asm.R11 (Asm.MBase Asm.RCX 1)
  , Asm.AluI Asm.OR Asm.R11 1
  , Asm.ShiftI Asm.SHL Asm.R11 wordShift
  , Asm.Alu Asm.SUB Asm.RSP Asm.R11
  , Asm.MovMR (Asm.MBase Asm.RSP 0) Asm.RSI
  , Asm.Test Asm.RCX Asm.RCX
  , Asm.Jcc Asm.E framed
  , Asm.Lea Asm.R9 (Asm.MBase Asm.RSP 8) ]
  ++ walk raws 8 save ++
  [ Asm.Lbl framed
  , Asm.Call (Linkage.Sym.label Linkage.Sym.SymAllocSlow)
  , Asm.MovRR Asm.RAX Asm.RDI
  , Asm.Lea Asm.RBX (area Linkage.Sym.SymScratch)
  , Asm.MovRM Asm.RSI (Asm.MBase Asm.RSP 0)
  -- NROOTS back to n, and the GC-visible slots reloaded from there
  , entry Asm.RCX gcCount
  , Asm.Lea Asm.R10 (area Linkage.Sym.SymNRoots)
  , Asm.MovRM Asm.R8 (Asm.MBase Asm.R10 0)
  , Asm.Alu Asm.SUB Asm.R8 Asm.RCX
  , Asm.MovMR (Asm.MBase Asm.R10 0) Asm.R8
  , Asm.ShiftI Asm.SHL Asm.R8 (cast Area.rootShift)
  , Asm.Lea Asm.R9 (area Linkage.Sym.SymRoots)
  , Asm.Alu Asm.ADD Asm.R9 Asm.R8
  , Asm.Lea Asm.RDX (Asm.MBase Asm.RSI (cast (LiveTable.slotsAt w)))
  , Asm.Test Asm.RCX Asm.RCX
  , Asm.Jcc Asm.E unrooted ]
  ++ walk unroots rootBytes reload ++
  [ Asm.Lbl unrooted
  , entry Asm.RCX rawCount
  , Asm.Test Asm.RCX Asm.RCX
  , Asm.Jcc Asm.E unframed
  , Asm.Lea Asm.R9 (Asm.MBase Asm.RSP 8) ]
  ++ walk unraws 8 reload ++
  [ Asm.Lbl unframed
  -- the frame given back
  , entry Asm.RCX rawCount
  , Asm.AluI Asm.ADD Asm.RCX 1
  , Asm.AluI Asm.OR Asm.RCX 1
  , Asm.ShiftI Asm.SHL Asm.RCX wordShift
  , Asm.Alu Asm.ADD Asm.RSP Asm.RCX
  , Asm.Ret ]
  where
    rooted, framed, unrooted, unframed, roots, raws, unroots, unraws : Asm.Label
    rooted = first
    framed = first + 1
    unrooted = first + 2
    unframed = first + 3
    roots = first + 4
    raws = first + 5
    unroots = first + 6
    unraws = first + 7

    area : Linkage.Sym -> Asm.Mem
    area s = Asm.MRip (Linkage.Sym.label s) 0

    -- the table's counts, by rsi, its address
    gcCount, rawCount : Asm.Mem
    gcCount = Asm.MBase Asm.RSI (cast (LiveTable.gcCountAt w))
    rawCount = Asm.MBase Asm.RSI (cast (LiveTable.rawCountAt w))

    -- an entry of the table into the register
    entry : Asm.Reg64 -> Asm.Mem -> Asm.Instr
    entry r = Asm.Load (AccessWidth.accessWidth w) False r

    rootBytes : Int
    rootBytes = cast (Area.rootOffset 1)

    -- a word's bytes, as the power of two they are
    wordShift : Bits8
    wordShift = 3

    -- for each of the rcx slots whose entries start at rdx: the slot's
    -- address in r11, then `move` between the slot and the word at r9,
    -- which moves on by `stride` each time
    walk : Asm.Label -> (stride : Int) -> (move : List Asm.Instr) -> List Asm.Instr
    walk l stride move =
      [ Asm.Lbl l
      , entry Asm.R11 (Asm.MBase Asm.RDX 0)
      , Asm.ShiftI Asm.SHL Asm.R11 (cast Area.slotShift)
      , Asm.Alu Asm.ADD Asm.R11 Asm.RBX ]
      ++ move ++
      [ Asm.AluI Asm.ADD Asm.R9 stride
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
