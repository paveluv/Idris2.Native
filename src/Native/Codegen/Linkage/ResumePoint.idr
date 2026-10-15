||| The shape of a resume point (`resumePoint`).
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Native.Codegen.Linkage.Routine` says what it is).
module Native.Codegen.Linkage.ResumePoint

import Data.List
import Native.Codegen.X86.Asm

%default total

||| A 16-aligned code label preceded by its layout word, as every resume
||| point and `idris_halt` need: pad to 8 mod 16, the word, the label.
export
resumePoint : X86.Asm.Label -> (layout : Integer) -> List X86.Asm.Instr
resumePoint l w = [X86.Asm.Align 16, X86.Asm.Bytes (replicate 8 0xCC), X86.Asm.Quad w, X86.Asm.Lbl l]
