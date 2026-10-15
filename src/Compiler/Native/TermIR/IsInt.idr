||| The integer types of the term IR (`IsInt`).
|||
||| Part of the term IR (`Compiler.Native.TermIR.Program` says what it is).
module Compiler.Native.TermIR.IsInt

import Compiler.Native.IRCommon.Ty as IRCommon
import HeapObj.Enc as HeapObj
import HeapObj.ValEnc

%default total

||| The integer types: arithmetic, comparisons and switches take two of one.
public export
data IsInt : IRCommon.Ty enc -> Type where
  IntW : IsInt IRCommon.Ty.W64
  IntF : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} -> IsInt (IRCommon.Ty.Fix {enc} {fx})
