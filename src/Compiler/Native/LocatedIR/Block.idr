||| A basic block of the located IR (`Block`).
|||
||| Part of the located IR (`Compiler.Native.LocatedIR.Program` says what it
||| is).
module Compiler.Native.LocatedIR.Block

import Compiler.Native.HeapObject.Enc
import Compiler.Native.LocatedIR.BlockLabel
import Compiler.Native.LocatedIR.BlockTerminator
import Compiler.Native.LocatedIR.Instr
import Compiler.Native.LocatedIR.Reg

%default total

||| A basic block. Only a resume block has parameters: its continuation's
||| `live` list followed by the result register. They declare what the block
||| receives; they do not define registers. Every other block reads the
||| registers set before it.
public export
record Block (enc : Enc) where
  constructor MkBlock
  label : BlockLabel
  params : List (Reg enc)
  body : List (Instr enc)
  term : BlockTerminator enc
