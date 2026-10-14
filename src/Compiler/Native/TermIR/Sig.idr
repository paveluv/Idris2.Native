||| What a caller knows of a function (`Sig`).
|||
||| Part of the term IR (`Compiler.Native.TermIR.Program` says what it is).
module Compiler.Native.TermIR.Sig

import Compiler.Native.HeapObject.Enc as HeapObject
import Compiler.Native.IRCommon.Conv as IRCommon
import Compiler.Native.IRCommon.Ty as IRCommon
import Core.Name

%default total

||| What a caller knows of a function.
public export
record Sig (enc : HeapObject.Enc) where
  constructor MkSig
  name : Name
  conv : IRCommon.Conv enc
  params : List (IRCommon.Ty enc)
  ||| Whether the function may convert between words and addresses, which
  ||| only the functions of the module implementing the runtime's memory
  ||| interface may: no word can be derived from a pointer elsewhere, which
  ||| is what lets the rooting stubs cover every pointer there is.
  converts : Bool
