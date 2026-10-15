||| A basic block of the located IR (`Block`).
|||
||| Part of the located IR (`Native.Codegen.LocatedIR.Program` says what it
||| is).
module Native.Codegen.LocatedIR.Block

import Native.Codegen.LocatedIR.Instr
import Native.Codegen.LocatedIR.Label
import Native.Codegen.LocatedIR.Reg
import Native.Codegen.LocatedIR.Terminator

import Native.HeapObj.Enc as HeapObj

%default total

||| A basic block. Only a resume block has parameters: its continuation's
||| `live` list followed by the result register. They declare what the block
||| receives; they do not define registers. Every other block reads the
||| registers set before it.
public export
record Block (enc : HeapObj.Enc) where
  constructor MkBlock
  label : Label
  params : List (Reg enc)
  body : List (Instr enc)
  term : Terminator enc
