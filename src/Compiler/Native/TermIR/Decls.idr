||| The program's declarations (`Decls`).
|||
||| Part of the term IR (`Compiler.Native.TermIR.Program` says what it is).
module Compiler.Native.TermIR.Decls

import Compiler.Native.TermIR.Sig
import Compiler.Native.TermIR.StaticSig

import HeapObj.Enc as HeapObj

%default total

||| The program's declarations: its functions, and the runtime's routines
||| it calls, and its statics.
public export
record Decls (enc : HeapObj.Enc) where
  constructor MkDecls
  sigs : List (Sig enc)
  statics : List StaticSig
