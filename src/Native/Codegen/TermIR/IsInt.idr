||| The integer types of the term IR (`IsInt`).
|||
||| Part of the term IR (`Native.Codegen.TermIR.Program` says what it is).
module Native.Codegen.TermIR.IsInt

import Native.Codegen.IRCommon.Ty as IRCommon
import Native.HeapObj.ValEnc
import Native.Types.Enc as Types

%default total

||| The integer types: arithmetic, comparisons and switches take two of one.
public export
data IsInt : IRCommon.Ty enc -> Type where
  IntW : IsInt IRCommon.Ty.W64
  IntF : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} -> IsInt (IRCommon.Ty.Fix {enc} {fx})
