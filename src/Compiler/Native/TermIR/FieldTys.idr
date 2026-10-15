||| The types of an object's fields, from its header (`fieldTys`), and the
||| headers the IR may allocate.
|||
||| Part of the term IR (`Compiler.Native.TermIR.Program` says what it is).
module Compiler.Native.TermIR.FieldTys

import Compiler.Native.IRCommon.Ty as IRCommon
import Data.List
import HeapObj.Enc as HeapObj
import HeapObj.Header as HeapObj
import HeapObj.Kind as HeapObj

%default total

||| The types of an object's fields, from its header: a closure's code
||| address and its filled arguments; a double's bits; a raw object's words.
public export
fieldTys : {0 k : HeapObj.Kind} -> HeapObj.Header enc k -> List (IRCommon.Ty enc)
fieldTys (HeapObj.Header.ConH _ a) = replicate a IRCommon.Ty.Val
fieldTys (HeapObj.Header.ClosureH _ f) = IRCommon.Ty.W64 :: replicate f IRCommon.Ty.Val
fieldTys HeapObj.Header.Int64H = [IRCommon.Ty.W64]
fieldTys HeapObj.Header.DoubleH = [IRCommon.Ty.F64]
fieldTys h@(HeapObj.Header.StringH _ _) = replicate (HeapObj.Header.fieldWords h) IRCommon.Ty.W64
fieldTys h@(HeapObj.Header.StringCharsH _) = replicate (HeapObj.Header.fieldWords h) IRCommon.Ty.W64
fieldTys (HeapObj.Header.BignumH _ n) = replicate n IRCommon.Ty.W64
fieldTys HeapObj.Header.IORefH = [IRCommon.Ty.Val]
fieldTys (HeapObj.Header.ArrayH n) = replicate n IRCommon.Ty.Val
fieldTys h@(HeapObj.Header.BufferH _) = replicate (HeapObj.Header.fieldWords h) IRCommon.Ty.W64
fieldTys HeapObj.Header.PtrH = [IRCommon.Ty.W64]

||| A header the IR may allocate: its parts fit their bits, and a closure has
||| fewer arguments filled than its arity.
public export
wellFormed : {0 k : HeapObj.Kind} -> HeapObj.Header enc k -> Bool
wellFormed h@(HeapObj.Header.ClosureH arity filled) = HeapObj.Header.fits h && filled < arity
wellFormed h = HeapObj.Header.fits h
