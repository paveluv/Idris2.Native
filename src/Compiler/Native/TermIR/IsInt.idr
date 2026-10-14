||| The integer types of the term IR (`IsInt`).
|||
||| Part of the term IR (`Compiler.Native.TermIR.Program` says what it is).
module Compiler.Native.TermIR.IsInt

import Compiler.Native.HeapObject.Enc
import Compiler.Native.HeapObject.ValEnc
import Compiler.Native.IRCommon.Ty

%default total

||| The integer types: arithmetic, comparisons and switches take two of one.
public export
data IsInt : Ty enc -> Type where
  IntW : IsInt W64
  IntF : {auto 0 fx : HasFixnums enc.val} -> IsInt (Fix {enc} {fx})
