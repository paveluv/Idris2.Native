||| A whole program of the located IR (`Program`).
|||
||| The located IR, the modules of `Compiler.Native.LocatedIR`: the native
||| backend's IR after register allocation, the input of the per-target
||| renderings into machine instructions. Producers do not write it: they
||| write the term IR (`Compiler.Native.TermIR.Program`), whose types make its rules
||| hold, and register allocation (`Compiler.Native.RegAlloc`) makes this IR
||| from it, computing every live list:
|||
|||     VMCode   -- lower --+
|||                         +--> term IR -- allocRegs --> located IR -- render --> machine code
|||     fragment -- lower --+
|||
||| Design rules:
|||
||| * Neutral about continuations. A non-tail call is one terminator that
|||   carries an abstract continuation (`Cont`): where to resume and what is
|||   live there. Nothing in the IR names a continuation register, a
|||   continuation object or a stack frame, so the same IR renders under
|||   either lowering of continuations (`Compiler.Native.Target.Lowering`).
||| * Target-independent. No instruction of any machine appears. Operations
|||   whose machine instructions differ per machine, such as materialising a constant,
|||   comparing and branching, or taking a code address, are IR instructions.
||| * Located. Every register is a `SCRATCH` slot, holding values of one type;
|||   the IR names no machine register, so none the target reserves can
|||   occur. Liveness is in the IR, in the `live` lists of `Cont`,
|||   `AllocObj`, `AllocSized` and `DirectCall`, and in a resume block's
|||   parameters, as the conversion computed it.
|||
||| The IR assumes what every target in scope provides: 64-bit words,
||| little-endian byte order, 8-byte aligned objects, IEEE 754 binary64
||| doubles, and a flat address space. A 32-bit target would change the
||| fixnum width and every offset.
|||
||| The objects the IR allocates and reads, and how a uniform value is a word,
||| are the heap-object model (`Compiler.Native.HeapObject.Header`), which the
||| IR builds on: the IR names kinds, headers and header parts, and
||| never a bit position or a size rule.
|||
||| Some names are chosen to differ from names in modules that a renderer
||| imports alongside it: `Rel`, `SubWord`, `Mem` and `Label`
||| from the x86 assembly ADT's `Cond`, `Width`, `Mem` and `Label`; `PtrTo`,
||| `Negate` and `Complement` from the Prelude's `Ptr`, `Neg` and `Not`.
module Compiler.Native.LocatedIR.Program

import Compiler.Native.LocatedIR.Function
import Compiler.Native.LocatedIR.Static

import Compiler.Native.HeapObject.Enc
import Compiler.Native.IRCommon.ConIds
import Compiler.Native.Target
import Core.Name

%default total

||| A whole program: its target, functions, statics, entry function and
||| constructor numbering.
public export
record Program (enc : Enc) where
  constructor MkProgram
  target : Target
  functions : List (Function enc)
  statics : List (Static enc)
  entry : Name
  conIds : ConIds
