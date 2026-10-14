||| The x86-64 target: `Compiler.Native.Target`'s parameters for x86-64
||| Linux. Registers are numbered by their encoding numbers (`regNum` and
||| `xmmNum` in `Compiler.Native.X86.Asm`), so the rendering and the encoder
||| agree on them by construction.
module Compiler.Native.X86.Target

import Compiler.Native.X86.Asm

import Compiler.Native.Target

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
  , lowering = HeapLowering
  , abi = MkAbi (map reg [RDI, RSI, RDX, RCX, R8, R9])
                (map (cast . xmmNum) [XMM0, XMM1, XMM2, XMM3, XMM4, XMM5, XMM6, XMM7])
  , returnReg = reg RAX
  , hp = reg R15
  , hplim = reg R14
  , k = reg R12
  , stackPointer = reg RSP
  , regName = \r => if r < 16 then show (regOfNum r) else "reg" ++ show r
  }
  where
    reg : Reg64 -> TargetReg
    reg r = cast (regNum r)
