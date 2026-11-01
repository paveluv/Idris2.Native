||| Where x86-64's rendering of each located instruction wants its register
||| operands and results (`row`, `Native.Codegen.Row`). The rendering
||| loads an operand into a register of its choice and stores a result
||| from one: a row names those registers, so that register allocation puts
||| the operand there before the instruction and takes the result from
||| there after, and the rendering finds them in place. An instruction
||| without a row here is rendered from wherever its operands are.
module Native.Codegen.X86.Rows

import Native.Codegen.X86.Asm
import Native.Codegen.X86.Target

import Data.List
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Codegen.LocatedIR.Instr as LocatedIR
import Native.Codegen.LocatedIR.Location as LocatedIR
import Native.Codegen.LocatedIR.Opnd as LocatedIR
import Native.Codegen.LocatedIR.Terminator as LocatedIR
import Native.Codegen.RegDesc
import Native.Codegen.RegMask
import Native.Codegen.Row
import Native.Codegen.Target
import Native.Rep
import Native.Types.Enc as Types

%default total

||| rax to r11, and xmm0 and xmm1, by their indices in x86-64's description
||| of its allocatable registers.
rax, rcx, rdx, rsi, rdi, r8, r9, r10, r11, xmm0, xmm1 : Row.Want
rax = Row.InRegister Rep.WordClass 0
rcx = Row.InRegister Rep.WordClass 1
rdx = Row.InRegister Rep.WordClass 2
rsi = Row.InRegister Rep.WordClass 3
rdi = Row.InRegister Rep.WordClass 4
r8 = Row.InRegister Rep.WordClass 5
r9 = Row.InRegister Rep.WordClass 6
r10 = Row.InRegister Rep.WordClass 7
r11 = Row.InRegister Rep.WordClass 8
xmm0 = Row.InRegister Rep.FloatClass 0
xmm1 = Row.InRegister Rep.FloatClass 1

||| The indices are the description's, checked here, by the typechecker.
0 indicesOk : take 9 Target.x86_64.allocatable.words
                = [ cast (Asm.regNum Asm.RAX), cast (Asm.regNum Asm.RCX), cast (Asm.regNum Asm.RDX)
                  , cast (Asm.regNum Asm.RSI), cast (Asm.regNum Asm.RDI), cast (Asm.regNum Asm.R8)
                  , cast (Asm.regNum Asm.R9), cast (Asm.regNum Asm.R10), cast (Asm.regNum Asm.R11) ]
indicesOk = Refl

0 floatIndicesOk : take 2 Target.x86_64.allocatable.floats
                     = [cast (Asm.xmmNum Asm.XMM0), cast (Asm.xmmNum Asm.XMM1)]
floatIndicesOk = Refl

||| What an operation writes besides its result: y's register, which an
||| immediate y is loaded into and a fixnum multiplication or shift turns
||| into y's value; and for a division, rdx, of the dividend's high word.
arith : IRCommon.Op.ArithOp -> RegMask
arith o = Row.clobbering (if division o then [rcx, rdx] else [rcx])
  where
    division : IRCommon.Op.ArithOp -> Bool
    division IRCommon.Op.DivS = True
    division IRCommon.Op.DivU = True
    division IRCommon.Op.RemS = True
    division IRCommon.Op.RemU = True
    division _ = False

||| What x86-64's rendering of each instruction writes of the allocatable
||| registers besides its results, given what a call may write (`called`,
||| the target's call model).
export
clobbers : (called : RegMask) -> LocatedIR.Instr enc -> RegMask
clobbers called i = case i of
  -- a double's bits, made in rax
  LocatedIR.Instr.FConst _ _ => Row.clobbering [rax]
  LocatedIR.Instr.Arith o _ _ _ => arith o
  LocatedIR.Instr.ArithOv o _ _ _ _ => arith o
  -- an immediate operand into rcx
  LocatedIR.Instr.Mul128 _ _ _ _ => Row.clobbering [rcx]
  LocatedIR.Instr.Div128 _ _ _ _ _ => Row.clobbering [rcx]
  -- the sign bit flipped in the double's bits, through rax and rcx
  LocatedIR.Instr.FNeg _ _ => Row.clobbering [rax, rcx]
  -- (in)equality's parity flag, in rcx
  LocatedIR.Instr.FCmp _ _ _ _ => Row.clobbering [rcx]
  -- an immediate or a static into rax or rcx
  LocatedIR.Instr.Cmp _ _ _ _ => Row.clobbering [rax, rcx]
  -- the address computed in the base's register, from the index shifted in
  -- its own; a double through rcx, which no want of a word register moves
  LocatedIR.Instr.Load _ _ _ => Row.clobbering [rax, rcx, rdx]
  LocatedIR.Instr.Store _ _ _ => Row.clobbering [rax, rcx, rdx]
  LocatedIR.Instr.LoadN _ _ _ _ => Row.clobbering [rax, rdx]
  LocatedIR.Instr.StoreN _ _ _ => Row.clobbering [rax, rdx]
  -- the collector may run, by a call
  LocatedIR.Instr.AllocObj _ _ _ _ => called
  LocatedIR.Instr.AllocSized _ _ _ _ _ => called
  LocatedIR.Instr.DirectCall _ _ _ _ _ => called
  -- the number and the arguments into the registers of Linux's convention,
  -- the result from rax; the kernel writes rcx and r11
  LocatedIR.Instr.SystemCall _ _ => Row.clobbering [rax, rcx, rdx, rsi, rdi, r8, r9, r10, r11]
  _ => RegMask.none

||| What x86-64's rendering of each terminator writes of the allocatable
||| registers. A terminator that leaves the function leaves nothing in its
||| registers: it writes what a call may (`called`).
export
termClobbers : (called : RegMask) -> LocatedIR.Terminator enc -> RegMask
termClobbers called t = case t of
  LocatedIR.Terminator.Jump _ => RegMask.none
  -- an immediate or a static into rax or rcx
  LocatedIR.Terminator.Branch _ _ _ _ _ => Row.clobbering [rax, rcx]
  -- a key too wide for an immediate, through rcx
  LocatedIR.Terminator.Switch _ _ _ => Row.clobbering [rcx]
  -- the first of the values tested, which the rest are combined into in
  -- turn, through rcx
  LocatedIR.Terminator.IfFixnums _ _ _ => Row.clobbering [rax, rcx]
  _ => called

||| The register of each class a parallel move's cycle is broken through
||| (`Native.Codegen.Sequentialise`): rcx, xmm1; never the register a move
||| between two slots goes through (`between`).
export
cycleTemp : Rep.RegClass -> Nat
cycleTemp c = case c of
  Rep.WordClass => 1
  Rep.FloatClass => 1

||| The wants of the operands that are locations, in their order.
located : List (LocatedIR.Opnd enc, Row.Want) -> List Row.Want
located [] = []
located ((LocatedIR.Opnd.R _, w) :: os) = w :: located os
located (_ :: os) = located os

||| The wants of a move, and of a retyping, which renders as one: its
||| operand into a register of its class when both ends are slots, since no
||| instruction moves between two places in memory; with a register at
||| either end, none.
between : LocatedIR.Location enc -> LocatedIR.Location enc -> List Row.Want
between (LocatedIR.Location.Slot _ _) (LocatedIR.Location.Slot _ t) =
  [case IRCommon.Ty.class t of Rep.WordClass => rax; Rep.FloatClass => xmm0]
between _ _ = []

||| Where x86-64's rendering of each instruction wants its register
||| operands and results, and what else it writes (`clobbers`).
export
row : (called : RegMask) -> LocatedIR.Instr enc -> Row
row called i = let (os, rs) = wants i in MkRow os rs (clobbers called i)
  where
    wants : LocatedIR.Instr enc -> (List Row.Want, List Row.Want)
    wants i' = case i' of
      LocatedIR.Instr.Const _ _ => ([], [rax])
      LocatedIR.Instr.CodeOf _ _ => ([], [rax])
      LocatedIR.Instr.StaticAddr _ _ => ([], [rax])
      LocatedIR.Instr.AreaAddr _ _ => ([], [rax])
      LocatedIR.Instr.Arith _ _ x y => (located [(x, rax), (y, rcx)], [rax])
      LocatedIR.Instr.ArithOv _ _ x y _ => (located [(x, rax), (y, rcx)], [rax])
      LocatedIR.Instr.TagOv _ _ _ => ([rax], [rax])
      LocatedIR.Instr.Mul128 _ _ x y => (located [(x, rax), (y, rcx)], [rdx, rax])
      LocatedIR.Instr.Div128 _ _ h l x => (located [(h, rdx), (l, rax), (x, rcx)], [rax, rdx])
      -- a narrowing loads its operand's slot narrowly: its operand stays
      LocatedIR.Instr.Ext _ _ _ _ => ([], [rax])
      LocatedIR.Instr.Convert IRCommon.Op.I2F _ _ => ([rax], [xmm0])
      LocatedIR.Instr.Convert IRCommon.Op.F2I _ _ => ([xmm0], [rax])
      LocatedIR.Instr.Convert IRCommon.Op.FBits _ _ => ([], [rax])
      LocatedIR.Instr.Convert IRCommon.Op.BitsF _ _ => ([rax], [])
      LocatedIR.Instr.FSqrt _ _ => ([xmm0], [xmm0])
      LocatedIR.Instr.FArith _ _ _ _ => ([xmm0, xmm1], [xmm0])
      LocatedIR.Instr.FCmp _ _ _ _ => ([xmm0, xmm1], [rdx])
      LocatedIR.Instr.Unary _ _ _ => ([rax], [rax])
      LocatedIR.Instr.Tag _ _ => ([rax], [rax])
      LocatedIR.Instr.Untag _ _ => ([rax], [rax])
      LocatedIR.Instr.Cmp _ _ x y => (located [(x, rax), (y, rcx)], [rdx])
      LocatedIR.Instr.Load _ _ _ => ([rax, rdx], [rcx])
      LocatedIR.Instr.Store _ _ _ => ([rcx, rax, rdx], [])
      LocatedIR.Instr.LoadN _ _ _ _ => ([rax, rdx], [rcx])
      LocatedIR.Instr.StoreN _ _ _ => ([rcx, rax, rdx], [])
      LocatedIR.Instr.LoadPart _ _ _ => ([rax], [rax])
      LocatedIR.Instr.Move d x => (between d x, [])
      LocatedIR.Instr.Narrow _ d x => (between d x, [])
      LocatedIR.Instr.Widen d x => (between d x, [])
      LocatedIR.Instr.AddrToWord d x => (between d x, [])
      LocatedIR.Instr.WordToAddr _ d x => (between d x, [])
      LocatedIR.Instr.ValToWord d x => (between d x, [])
      LocatedIR.Instr.WordToVal d x => (between d x, [])
      _ => ([], [])

||| Where x86-64's rendering of each terminator wants its register
||| operands, and what it writes (`termClobbers`). A call's arguments and a
||| direct call's results travel where `Target.place` puts them, the words
||| of `ARGS` through rax and rcx, and a non-tail application allocates its
||| continuation before it reads its operands: their operands stay where
||| they are.
export
termRow : (called : RegMask) -> LocatedIR.Terminator enc -> Row
termRow called t = MkRow (wants t) [] (termClobbers called t)
  where
    wants : LocatedIR.Terminator enc -> List Row.Want
    wants t' = case t' of
      LocatedIR.Terminator.Branch _ x y _ _ => located [(x, rax), (y, rcx)]
      LocatedIR.Terminator.Switch _ _ _ => [rax]
      -- the first of the values tested; the rest are read in turn through rcx
      LocatedIR.Terminator.IfFixnums _ _ _ => [rax]
      LocatedIR.Terminator.Return x => located [(x, rax)]
      LocatedIR.Terminator.TailApply _ _ => [rdi, rsi]
      _ => []
