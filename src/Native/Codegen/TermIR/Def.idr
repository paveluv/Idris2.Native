||| A function's definition (`Def`).
|||
||| Part of the term IR (`Native.Codegen.TermIR.Program` says what it is).
module Native.Codegen.TermIR.Def

import Native.Codegen.TermIR.Body
import Native.Codegen.TermIR.Decls
import Native.Codegen.TermIR.Sig

import Core.Name
import Native.Codegen.IRCommon.Conv
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.HeapObj.Enc as HeapObj

%default total

||| A function's definition: a body over its parameters, or a Direct routine
||| of the runtime, outside the program.
public export
data Def : Decls enc -> Sig enc -> Type where
  Defined : Body d s.conv s.converts [] s.params -> Def d s
  External : Def d (Sig.MkSig n (IRCommon.Conv.Direct rs col) ps False)
