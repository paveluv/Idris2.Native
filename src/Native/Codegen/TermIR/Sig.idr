||| What a caller knows of a function (`Sig`).
|||
||| Part of the term IR (`Native.Codegen.TermIR.Program` says what it is).
module Native.Codegen.TermIR.Sig

import Core.Name
import Native.Codegen.IRCommon.Conv as IRCommon
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Types.Enc as Types

%default total

||| What a caller knows of a function.
public export
record Sig (enc : Types.Enc) where
  constructor MkSig
  name : Name
  conv : IRCommon.Conv enc
  params : List (IRCommon.Ty enc)
  ||| Whether the function may convert between words and addresses, which
  ||| only the functions of the module implementing the runtime's memory
  ||| interface may: no word can be derived from a pointer elsewhere, which
  ||| is what lets the rooting stubs cover every pointer there is.
  converts : Bool
