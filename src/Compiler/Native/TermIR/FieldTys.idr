||| The types of an object's fields, from its header (`fieldTys`), and the
||| headers the IR may allocate.
|||
||| Part of the term IR (`Compiler.Native.TermIR.Program` says what it is).
module Compiler.Native.TermIR.FieldTys

import Compiler.Native.HeapObject.Enc as HeapObject
import Compiler.Native.HeapObject.Header as HeapObject
import Compiler.Native.HeapObject.Kind as HeapObject
import Compiler.Native.IRCommon.Ty as IRCommon
import Data.List

%default total

||| The types of an object's fields, from its header: a closure's code
||| address and its filled arguments; a double's bits; a raw object's words.
public export
fieldTys : {0 k : HeapObject.Kind} -> HeapObject.Header enc k -> List (IRCommon.Ty enc)
fieldTys (HeapObject.Header.ConH _ a) = replicate a IRCommon.Ty.Val
fieldTys (HeapObject.Header.ClosureH _ f) = IRCommon.Ty.W64 :: replicate f IRCommon.Ty.Val
fieldTys HeapObject.Header.Int64H = [IRCommon.Ty.W64]
fieldTys HeapObject.Header.DoubleH = [IRCommon.Ty.F64]
fieldTys h@(HeapObject.Header.StringH _ _) = replicate (HeapObject.Header.fieldWords h) IRCommon.Ty.W64
fieldTys h@(HeapObject.Header.StringCharsH _) = replicate (HeapObject.Header.fieldWords h) IRCommon.Ty.W64
fieldTys (HeapObject.Header.BignumH _ n) = replicate n IRCommon.Ty.W64
fieldTys HeapObject.Header.IORefH = [IRCommon.Ty.Val]
fieldTys (HeapObject.Header.ArrayH n) = replicate n IRCommon.Ty.Val
fieldTys h@(HeapObject.Header.BufferH _) = replicate (HeapObject.Header.fieldWords h) IRCommon.Ty.W64
fieldTys HeapObject.Header.PtrH = [IRCommon.Ty.W64]

||| A header the IR may allocate: its parts fit their bits, and a closure has
||| fewer arguments filled than its arity.
public export
wellFormed : {0 k : HeapObject.Kind} -> HeapObject.Header enc k -> Bool
wellFormed h@(HeapObject.Header.ClosureH arity filled) = HeapObject.Header.fits h && filled < arity
wellFormed h = HeapObject.Header.fits h
