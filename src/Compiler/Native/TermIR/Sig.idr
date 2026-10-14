||| What a caller knows of a function (`Sig`).
|||
||| Part of the term IR (`Compiler.Native.TermIR.Program` says what it is).
module Compiler.Native.TermIR.Sig

import Compiler.Native.HeapObject.Enc
import Compiler.Native.IRCommon.Conv
import Compiler.Native.IRCommon.Ty
import Core.Name

%default total

||| What a caller knows of a function.
public export
record Sig (enc : Enc) where
  constructor MkSig
  name : Name
  conv : Conv enc
  params : List (Ty enc)
  ||| Whether the function may convert between words and addresses, which
  ||| only the functions of the module implementing the runtime's memory
  ||| interface may: no word can be derived from a pointer elsewhere, which
  ||| is what lets the rooting stubs cover every pointer there is.
  converts : Bool
