||| The x86-64 access width of a sub-word (`accessWidth`): what a narrow
||| load or store of it reads or writes.
module Native.Codegen.X86.AccessWidth

import Native.Codegen.X86.Asm

import Native.Width

%default total

||| The access width of a sub-word.
export
accessWidth : Width.SubWord -> Asm.Width
accessWidth Width.Sub8 = Asm.W8
accessWidth Width.Sub16 = Asm.W16
accessWidth Width.Sub32 = Asm.W32
