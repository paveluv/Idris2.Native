||| The program's declarations (`Decls`).
|||
||| Part of the term IR (`Native.Codegen.TermIR.Program` says what it is).
module Native.Codegen.TermIR.Decls

import Native.Codegen.TermIR.Sig
import Native.Codegen.TermIR.StaticSig

import Native.HeapObj.Enc as HeapObj

%default total

||| The program's declarations: its functions, and the runtime's routines
||| it calls, and its statics.
public export
record Decls (enc : HeapObj.Enc) where
  constructor MkDecls
  sigs : List (Sig enc)
  statics : List StaticSig
