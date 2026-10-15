||| The x86-64 target: `Native.Codegen.Target`'s parameters for x86-64
||| Linux. Registers are numbered by their encoding numbers (`regNum` and
||| `xmmNum` in `Native.Codegen.X86.Asm`), so the rendering and the encoder
||| agree on them by construction.
module Native.Codegen.X86.Target

import Native.Codegen.X86.Asm

import Native.Codegen.Target

%default total

||| x86-64 Linux under the heap lowering. Values pass in the SysV argument
||| registers, word and floating-point, and a `Direct` function returns its
||| results in them too, where SysV would use rax and rdx. `hp`,
||| `hplim` and `k` are r15, r14 and r12, which are callee-saved under SysV,
||| so C code preserves them.
public export
x86_64 : Target
x86_64 = Target.MkTarget
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
  }
  where
    reg : Asm.Reg64 -> Target.TargetReg
    reg r = cast (Asm.regNum r)
