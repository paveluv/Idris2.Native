||| A function's definition (`Def`).
|||
||| Part of the term IR (`Compiler.Native.TermIR.Program` says what it is).
module Compiler.Native.TermIR.Def

import Compiler.Native.TermIR.Body
import Compiler.Native.TermIR.Decls
import Compiler.Native.TermIR.Sig

import Compiler.Native.HeapObject.Enc as HeapObject
import Compiler.Native.IRCommon.Conv
import Compiler.Native.IRCommon.Ty as IRCommon
import Core.Name

%default total

||| A function's definition: a body over its parameters, or a Direct routine
||| of the runtime, outside the program.
public export
data Def : Decls enc -> Sig enc -> Type where
  Defined : Body d s.conv s.converts [] s.params -> Def d s
  External : Def d (Sig.MkSig n (IRCommon.Conv.Direct rs col) ps False)
