||| A function's convention (`Conv`).
|||
||| Part of the term IR (`Compiler.Native.TermIR.Program` says what it is).
module Compiler.Native.TermIR.Conv

import Compiler.Native.HeapObject.Enc
import Compiler.Native.IRCommon.Ty

%default total

||| A function's convention. A Direct function declares its results, and
||| whether a call of it may start a collection.
public export
data Conv : Enc -> Type where
  InCPS : Conv enc
  InDirect : (results : List (Ty enc)) -> (collects : Bool) -> Conv enc
