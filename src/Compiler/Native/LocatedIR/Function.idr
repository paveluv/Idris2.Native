||| A function of the located IR (`Function`).
|||
||| Part of the located IR (`Compiler.Native.LocatedIR.Program` says what it
||| is).
module Compiler.Native.LocatedIR.Function

import Compiler.Native.LocatedIR.Block
import Compiler.Native.LocatedIR.Label
import Compiler.Native.LocatedIR.Reg

import Compiler.Native.IRCommon.Conv as IRCommon
import Core.FC
import Core.Name
import HeapObj.Enc as HeapObj

%default total

||| A function: its convention, the term IR's, its parameters in argument
||| order, its entry block, and its blocks. `fc` is its source location, for
||| dumps. A `Direct` function returns the results its convention declares
||| by `Ret`, passed as arguments are (`Compiler.Native.Target.place`); a CPS
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
