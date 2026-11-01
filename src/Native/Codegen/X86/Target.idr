||| The x86-64 target: `Native.Codegen.Target`'s parameters for x86-64
||| Linux. Registers are numbered by their encoding numbers (`regNum` and
||| `xmmNum` in `Native.Codegen.X86.Asm`), so the rendering and the encoder
||| agree on them by construction.
module Native.Codegen.X86.Target

import Native.Codegen.X86.Asm

import Native.Codegen.RegDesc
import Native.Codegen.Target

%default total

||| x86-64 Linux under the heap lowering. Values pass in the SysV argument
||| registers, word and floating-point, and a `Direct` function returns its
||| results in them too, where SysV would use rax and rdx. `hp`,
||| `hplim` and `k` are r15, r14 and r12, which are callee-saved under SysV,
||| so C code preserves them.
public export
x86_64 : Target
x86_64 = MkTarget
  { name = "x86-64"
  , wordSize = 8
  , lowering = Target.HeapLowering
  , abi = Target.MkAbi (map reg [Asm.RDI, Asm.RSI, Asm.RDX, Asm.RCX, Asm.R8, Asm.R9])
                (map (cast . Asm.xmmNum)
                  [Asm.XMM0, Asm.XMM1, Asm.XMM2, Asm.XMM3, Asm.XMM4, Asm.XMM5, Asm.XMM6, Asm.XMM7])
  , returnReg = reg Asm.RAX
  , hp = reg Asm.R15
  , hplim = reg Asm.R14
  , k = reg Asm.R12
  , stackPointer = reg Asm.RSP
  , regName = \r => if r < 16 then show (Asm.regOfNum r) else "reg" ++ show r
  , allocatable = RegDesc.regDesc
                    (map reg [ Asm.RAX, Asm.RCX, Asm.RDX, Asm.RSI, Asm.RDI, Asm.R8, Asm.R9
                             , Asm.R10, Asm.R11, Asm.R13, Asm.RBP ])
                    (map (cast . Asm.xmmNum)
                      [ Asm.XMM0, Asm.XMM1, Asm.XMM2, Asm.XMM3, Asm.XMM4, Asm.XMM5, Asm.XMM6
                      , Asm.XMM7, Asm.XMM8, Asm.XMM9, Asm.XMM10, Asm.XMM11, Asm.XMM12, Asm.XMM13
                      , Asm.XMM14, Asm.XMM15 ])
  , slotBase = reg Asm.RBX
  }
  where
    reg : Asm.Reg64 -> Target.TargetReg
    reg r = cast (Asm.regNum r)

||| The description is sound: checked here, by the typechecker.
0 x86_64WellFormed : Target.wellFormed X86.Target.x86_64 = True
x86_64WellFormed = Refl
