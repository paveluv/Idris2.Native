||| The types of an object's fields, from its header (`fieldTys`), and the
||| headers the IR may allocate.
|||
||| Part of the term IR (`Compiler.Native.TermIR.Program` says what it is).
module Compiler.Native.TermIR.FieldTys

import Compiler.Native.HeapObject.Enc
import Compiler.Native.HeapObject.Header
import Compiler.Native.HeapObject.Kind
import Compiler.Native.IRCommon.Ty
import Data.List

%default total

||| The types of an object's fields, from its header: a closure's code
||| address and its filled arguments; a double's bits; a raw object's words.
public export
fieldTys : {0 k : Kind} -> Header enc k -> List (Ty enc)
fieldTys (ConH _ a) = replicate a Val
fieldTys (ClosureH _ f) = W64 :: replicate f Val
fieldTys Int64H = [W64]
fieldTys DoubleH = [F64]
fieldTys h@(StringH _ _) = replicate (fieldWords h) W64
fieldTys h@(StringCharsH _) = replicate (fieldWords h) W64
fieldTys (BignumH _ n) = replicate n W64
fieldTys IORefH = [Val]
fieldTys (ArrayH n) = replicate n Val
fieldTys h@(BufferH _) = replicate (fieldWords h) W64
fieldTys PtrH = [W64]

||| A header the IR may allocate: its parts fit their bits, and a closure has
||| fewer arguments filled than its arity.
public export
wellFormed : {0 k : Kind} -> Header enc k -> Bool
wellFormed h@(ClosureH arity filled) = fits h && filled < arity
wellFormed h = fits h
