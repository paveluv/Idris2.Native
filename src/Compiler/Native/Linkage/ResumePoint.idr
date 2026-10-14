||| The shape of a resume point (`resumePoint`).
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Compiler.Native.Linkage.Routine` says what it is).
module Compiler.Native.Linkage.ResumePoint

import Compiler.Native.X86.Asm
import Data.List

%default total

||| A 16-aligned code label preceded by its layout word, as every resume
||| point and `idris_halt` need: pad to 8 mod 16, the word, the label.
export
resumePoint : Label -> (layout : Integer) -> List Instr
resumePoint l w = [Align 16, Bytes (replicate 8 0xCC), Quad w, Lbl l]
