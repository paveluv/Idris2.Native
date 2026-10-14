||| The integer types of the term IR (`IsInt`).
|||
||| Part of the term IR (`Compiler.Native.TermIR.Program` says what it is).
module Compiler.Native.TermIR.IsInt

import Compiler.Native.HeapObject.Enc as HeapObject
import Compiler.Native.HeapObject.ValEnc
import Compiler.Native.IRCommon.Ty as IRCommon

%default total

||| The integer types: arithmetic, comparisons and switches take two of one.
public export
data IsInt : IRCommon.Ty enc -> Type where
  IntW : IsInt IRCommon.Ty.W64
  IntF : {auto 0 fx : HeapObject.ValEnc.HasFixnums enc.val} -> IsInt (IRCommon.Ty.Fix {enc} {fx})
