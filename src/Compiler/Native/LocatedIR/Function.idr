||| A function of the located IR (`Function`).
|||
||| Part of the located IR (`Compiler.Native.LocatedIR.Program` says what it
||| is).
module Compiler.Native.LocatedIR.Function

import Compiler.Native.HeapObject.Enc
import Compiler.Native.IRCommon.Ty
import Compiler.Native.LocatedIR.Block
import Compiler.Native.LocatedIR.BlockLabel
import Compiler.Native.LocatedIR.CallingConvention
import Compiler.Native.LocatedIR.Reg
import Core.FC
import Core.Name

%default total

||| A function: its convention, its parameters in argument order, the types
||| of its results, its entry block, and its blocks. `fc` is its source
||| location, for dumps. A `Direct` function returns its results by `Ret`,
||| passed as arguments are (`Compiler.Native.Target.place`); a CPS function
||| has none, and delivers one `Val` to its continuation by `Return`.
public export
record Function (enc : Enc) where
  constructor MkFunction
  name : Name
  conv : CallingConvention
  params : List (Reg enc)
  results : List (Ty enc)
  entry : BlockLabel
  blocks : List (Block enc)
  fc : FC
