||| The registers each x86-64 instruction writes (`writes`), the implicit
||| ones included: the stack pointer of a push, a pop, a call and a return;
||| rdx of `cqo`; rax and rdx of a division and of `mul`; rax, rcx and r11
||| of a system call, which returns in rax and leaves the return address in
||| rcx and the flags in r11; rax of `lock cmpxchg`, which loads it when
||| the exchange fails.
|||
||| A write that may not happen, or may leave the register as it was,
||| counts as a write: `cmov`'s, `setcc`'s (of the low byte only) and
||| `lock cmpxchg`'s. A call writes the stack pointer as an instruction;
||| what its callee writes is the callee's. Memory and the flags are not
||| registers here, and a directive writes nothing.
|||
||| The table is the register allocator's trusted description of the
||| machine: what an instruction may destroy. tests/native/writes001 runs
||| every form on the machine and checks that each register that changes is
||| one the table names.
module Native.Codegen.X86.Writes

import Native.Codegen.X86.Asm
import Native.Codegen.X86.RegSet

%default total

export
writes : Asm.Instr -> RegSet
writes i = case i of
  Asm.MovRR d _ => RegSet.gpr d
  Asm.MovRI d _ => RegSet.gpr d
  Asm.MovRM d _ => RegSet.gpr d
  Asm.MovMR _ _ => RegSet.none
  Asm.MovMI _ _ => RegSet.none
  Asm.Lea d _ => RegSet.gpr d
  Asm.Load _ _ d _ => RegSet.gpr d
  Asm.Store _ _ _ => RegSet.none
  Asm.Alu Asm.CMP _ _ => RegSet.none
  Asm.Alu _ d _ => RegSet.gpr d
  Asm.AluI Asm.CMP _ _ => RegSet.none
  Asm.AluI _ d _ => RegSet.gpr d
  Asm.AluRM Asm.CMP _ _ => RegSet.none
  Asm.AluRM _ d _ => RegSet.gpr d
  Asm.AluMR _ _ _ => RegSet.none
  Asm.Test _ _ => RegSet.none
  Asm.TestI _ _ => RegSet.none
  Asm.Imul d _ => RegSet.gpr d
  Asm.ImulI d _ _ => RegSet.gpr d
  Asm.Cqo => RegSet.gpr Asm.RDX
  Asm.Idiv _ => RegSet.gprs [Asm.RAX, Asm.RDX]
  Asm.DivU _ => RegSet.gprs [Asm.RAX, Asm.RDX]
  Asm.Mul _ => RegSet.gprs [Asm.RAX, Asm.RDX]
  Asm.Neg r => RegSet.gpr r
  Asm.Not r => RegSet.gpr r
  Asm.ShiftI _ r _ => RegSet.gpr r
  Asm.ShiftCl _ r => RegSet.gpr r
  Asm.Jmp _ => RegSet.none
  Asm.Jcc _ _ => RegSet.none
  Asm.Call _ => RegSet.gpr Asm.RSP
  Asm.JmpR _ => RegSet.none
  Asm.JmpM _ => RegSet.none
  Asm.CallR _ => RegSet.gpr Asm.RSP
  Asm.Ret => RegSet.gpr Asm.RSP
  Asm.Push _ => RegSet.gpr Asm.RSP
  Asm.Pop r => RegSet.gprs [r, Asm.RSP]
  Asm.Setcc _ r => RegSet.gpr r
  Asm.Cmov _ d _ => RegSet.gpr d
  Asm.MovsdRM x _ => RegSet.xmm x
  Asm.MovsdMR _ _ => RegSet.none
  Asm.MovsdRR x _ => RegSet.xmm x
  Asm.Sse _ x _ => RegSet.xmm x
  Asm.Ucomisd _ _ => RegSet.none
  Asm.Cvtsi2sd x _ => RegSet.xmm x
  Asm.Cvttsd2si r _ => RegSet.gpr r
  Asm.MovqXR x _ => RegSet.xmm x
  Asm.MovqRX r _ => RegSet.gpr r
  Asm.Syscall => RegSet.gprs [Asm.RAX, Asm.RCX, Asm.R11]
  Asm.LockCmpxchg _ _ => RegSet.gpr Asm.RAX
  Asm.Nop => RegSet.none
  Asm.Int3 => RegSet.none
  Asm.Lbl _ => RegSet.none
  Asm.Align _ => RegSet.none
  Asm.Quad _ => RegSet.none
  Asm.Bytes _ => RegSet.none
  Asm.Comment _ => RegSet.none
