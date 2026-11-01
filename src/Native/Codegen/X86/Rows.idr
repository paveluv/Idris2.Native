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
import Native.Codegen.LocatedIR.Instr as LocatedIR
import Native.Codegen.LocatedIR.Opnd as LocatedIR
import Native.Codegen.LocatedIR.Terminator as LocatedIR
import Native.Codegen.RegDesc
import Native.Codegen.Row
import Native.Codegen.Target
import Native.Rep
import Native.Types.Enc as Types

%default total

||| rax, rcx, rdx, rsi and rdi, and xmm0 and xmm1, by their indices in x86-64's
||| description of its allocatable registers.
rax, rcx, rdx, rsi, rdi, xmm0, xmm1 : Row.Want
rax = Row.InRegister Rep.WordClass 0
rcx = Row.InRegister Rep.WordClass 1
rdx = Row.InRegister Rep.WordClass 2
rsi = Row.InRegister Rep.WordClass 3
rdi = Row.InRegister Rep.WordClass 4
xmm0 = Row.InRegister Rep.FloatClass 0
xmm1 = Row.InRegister Rep.FloatClass 1

||| The indices are the description's, checked here, by the typechecker.
0 indicesOk : take 5 Target.x86_64.allocatable.words
                = [ cast (Asm.regNum Asm.RAX), cast (Asm.regNum Asm.RCX), cast (Asm.regNum Asm.RDX)
                  , cast (Asm.regNum Asm.RSI), cast (Asm.regNum Asm.RDI) ]
indicesOk = Refl

0 floatIndicesOk : take 2 Target.x86_64.allocatable.floats
                     = [cast (Asm.xmmNum Asm.XMM0), cast (Asm.xmmNum Asm.XMM1)]
floatIndicesOk = Refl

||| The wants of the operands that are locations, in their order.
located : List (LocatedIR.Opnd enc, Row.Want) -> List Row.Want
located [] = []
located ((LocatedIR.Opnd.R _, w) :: os) = w :: located os
located (_ :: os) = located os

||| Where x86-64's rendering of each instruction wants its register
||| operands and results.
export
row : LocatedIR.Instr enc -> Row
row i = case i of
  LocatedIR.Instr.Const _ _ => MkRow [] [rax]
  LocatedIR.Instr.CodeOf _ _ => MkRow [] [rax]
  LocatedIR.Instr.StaticAddr _ _ => MkRow [] [rax]
  LocatedIR.Instr.AreaAddr _ _ => MkRow [] [rax]
  LocatedIR.Instr.Arith _ _ x y => MkRow (located [(x, rax), (y, rcx)]) [rax]
  LocatedIR.Instr.ArithOv _ _ x y _ => MkRow (located [(x, rax), (y, rcx)]) [rax]
  LocatedIR.Instr.TagOv _ _ _ => MkRow [rax] [rax]
  LocatedIR.Instr.Mul128 _ _ x y => MkRow (located [(x, rax), (y, rcx)]) [rdx, rax]
  LocatedIR.Instr.Div128 _ _ h l x => MkRow (located [(h, rdx), (l, rax), (x, rcx)]) [rax, rdx]
  -- a narrowing loads its operand's slot narrowly: its operand stays
  LocatedIR.Instr.Ext _ _ _ _ => MkRow [] [rax]
  LocatedIR.Instr.Convert IRCommon.Op.I2F _ _ => MkRow [rax] [xmm0]
  LocatedIR.Instr.Convert IRCommon.Op.F2I _ _ => MkRow [xmm0] [rax]
  LocatedIR.Instr.Convert IRCommon.Op.FBits _ _ => MkRow [] [rax]
  LocatedIR.Instr.Convert IRCommon.Op.BitsF _ _ => MkRow [rax] []
  LocatedIR.Instr.FSqrt _ _ => MkRow [xmm0] [xmm0]
  LocatedIR.Instr.FArith _ _ _ _ => MkRow [xmm0, xmm1] [xmm0]
  LocatedIR.Instr.FCmp _ _ _ _ => MkRow [xmm0, xmm1] [rdx]
  LocatedIR.Instr.Unary _ _ _ => MkRow [rax] [rax]
  LocatedIR.Instr.Tag _ _ => MkRow [rax] [rax]
  LocatedIR.Instr.Untag _ _ => MkRow [rax] [rax]
  LocatedIR.Instr.Cmp _ _ x y => MkRow (located [(x, rax), (y, rcx)]) [rdx]
  LocatedIR.Instr.Load _ _ _ => MkRow [rax, rdx] [rcx]
  LocatedIR.Instr.Store _ _ _ => MkRow [rcx, rax, rdx] []
  LocatedIR.Instr.LoadN _ _ _ _ => MkRow [rax, rdx] [rcx]
  LocatedIR.Instr.StoreN _ _ _ => MkRow [rcx, rax, rdx] []
  LocatedIR.Instr.LoadPart _ _ _ => MkRow [rax] [rax]
  _ => Row.anywhere

||| Where x86-64's rendering of each terminator wants its register
||| operands. A call's arguments and a direct call's results travel where
||| `Target.place` puts them, the words of `ARGS` through rax and rcx, and
||| a non-tail application allocates its continuation before it reads its
||| operands: their operands stay where they are.
export
termRow : LocatedIR.Terminator enc -> Row
termRow t = case t of
  LocatedIR.Terminator.Branch _ x y _ _ => MkRow (located [(x, rax), (y, rcx)]) []
  LocatedIR.Terminator.Switch _ _ _ => MkRow [rax] []
  -- the first of the values tested; the rest are read in turn through rcx
  LocatedIR.Terminator.IfFixnums _ _ _ => MkRow [rax] []
  LocatedIR.Terminator.Return x => MkRow (located [(x, rax)]) []
  LocatedIR.Terminator.TailApply _ _ => MkRow [rdi, rsi] []
  _ => Row.anywhere
