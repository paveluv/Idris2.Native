||| The operations that have an overflow form (`OvOp`).
|||
||| Part of the term IR (`Compiler.Native.TermIR.Program` says what it is).
module Compiler.Native.TermIR.OvOp

import Compiler.Native.IRCommon.Op

%default total

||| The operations that have an overflow form.
public export
data OvOp = OvAdd | OvSub | OvMul

public export
ovArith : OvOp -> IRCommon.Op.ArithOp
ovArith OvAdd = IRCommon.Op.Add
ovArith OvSub = IRCommon.Op.Sub
ovArith OvMul = IRCommon.Op.Mul
