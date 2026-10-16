||| The types of an object's fields, from its header (`fieldTys`), and the
||| headers the IR may allocate.
|||
||| Part of the term IR (`Native.Codegen.TermIR.Program` says what it is).
module Native.Codegen.TermIR.FieldTys

import Data.List
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Types.Enc as Types
import Native.Types.Header as Types
import Native.Types.Kind as Types

%default total

||| The types of an object's fields, from its header: a closure's code
||| address and its filled arguments; a double's bits; a raw object's words.
public export
fieldTys : {0 k : Types.Kind} -> Types.Header enc k -> List (IRCommon.Ty enc)
fieldTys (Types.Header.ConH _ a) = replicate a IRCommon.Ty.Val
fieldTys (Types.Header.ClosureH _ f) = IRCommon.Ty.W64 :: replicate f IRCommon.Ty.Val
fieldTys Types.Header.Int64H = [IRCommon.Ty.W64]
fieldTys Types.Header.DoubleH = [IRCommon.Ty.F64]
fieldTys h@(Types.Header.StringH _ _) = replicate (Types.Header.fieldWords h) IRCommon.Ty.W64
fieldTys h@(Types.Header.StringCharsH _) = replicate (Types.Header.fieldWords h) IRCommon.Ty.W64
fieldTys (Types.Header.BignumH _ n) = replicate n IRCommon.Ty.W64
fieldTys Types.Header.IORefH = [IRCommon.Ty.Val]
fieldTys (Types.Header.ArrayH n) = replicate n IRCommon.Ty.Val
fieldTys h@(Types.Header.BufferH _) = replicate (Types.Header.fieldWords h) IRCommon.Ty.W64
fieldTys Types.Header.PtrH = [IRCommon.Ty.W64]

||| A header the IR may allocate: its parts fit their bits, and a closure has
||| fewer arguments filled than its arity.
public export
wellFormed : {0 k : Types.Kind} -> Types.Header enc k -> Bool
wellFormed h@(Types.Header.ClosureH arity filled) = Types.Header.fits h && filled < arity
wellFormed h = Types.Header.fits h
