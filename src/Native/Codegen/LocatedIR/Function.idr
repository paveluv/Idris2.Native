||| A function of the located IR (`Function`).
|||
||| Part of the located IR (`Native.Codegen.LocatedIR.Program` says what it
||| is).
module Native.Codegen.LocatedIR.Function

import Native.Codegen.LocatedIR.Block
import Native.Codegen.LocatedIR.Label
import Native.Codegen.LocatedIR.Reg

import Core.FC
import Core.Name
import Native.Codegen.IRCommon.Conv as IRCommon
import Native.HeapObj.Enc as HeapObj

%default total

||| A function: its convention, the term IR's, its parameters in argument
||| order, its entry block, and its blocks. `fc` is its source location, for
||| dumps. A `Direct` function returns the results its convention declares
||| by `Ret`, passed as arguments are (`Native.Codegen.Target.place`); a CPS
||| function has none, and delivers one `Val` to its continuation by
||| `Return`.
public export
record Function (enc : HeapObj.Enc) where
  constructor MkFunction
  name : Name
  conv : IRCommon.Conv enc
  params : List (Reg enc)
  entry : Label
  blocks : List (Block enc)
  fc : FC
