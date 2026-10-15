||| The operations that have an overflow form (`OvOp`).
|||
||| Part of the term IR (`Native.Codegen.TermIR.Program` says what it is).
module Native.Codegen.TermIR.OvOp

import Native.Codegen.IRCommon.Op

%default total

||| The operations that have an overflow form.
public export
data OvOp = OvAdd | OvSub | OvMul

public export
ovArith : OvOp -> IRCommon.Op.ArithOp
ovArith OvAdd = IRCommon.Op.Add
ovArith OvSub = IRCommon.Op.Sub
ovArith OvMul = IRCommon.Op.Mul
