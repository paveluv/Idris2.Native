||| The parts of a header that alone decide an object's size (`Sizes`), and
||| what fills an object of a run-time size.
|||
||| Part of the term IR (`Compiler.Native.TermIR.Program` says what it is).
module Compiler.Native.TermIR.Sizes

import Compiler.Native.TermIR.Opnd

import Compiler.Native.IRCommon.Ty as IRCommon
import HeapObj.Enc as HeapObj
import HeapObj.Header
import HeapObj.Kind as HeapObj

%default total

||| The parts that alone decide an object's size.
public export
data Sizes : HeapObj.Header.HeaderPart k -> Type where
  SizesArray : Sizes HeapObj.Header.ArrayElems
  SizesString : Sizes HeapObj.Header.StringBytes
  SizesStringChars : Sizes HeapObj.Header.StringChars
  SizesBuffer : Sizes HeapObj.Header.BufferBytes

||| What fills a new object of a run-time size, by the part that sizes it: a
||| `Val` for every element of an `ARRAY`, which the collector scans;
||| nothing for the raw kinds, whose bytes are left as they are. A part that
||| sizes nothing (`Sizes` has no proof for it) takes nothing.
public export
Fill : (IRCommon.Ty enc -> Type) -> HeapObj.Header.HeaderPart k -> Type
Fill var HeapObj.Header.ArrayElems = Opnd var IRCommon.Ty.Val
Fill var HeapObj.Header.StringAscii = ()
Fill var HeapObj.Header.StringBytes = ()
Fill var HeapObj.Header.StringChars = ()
Fill var HeapObj.Header.BufferBytes = ()
Fill var HeapObj.Header.ConId = ()
Fill var HeapObj.Header.ConArity = ()
Fill var HeapObj.Header.ClosureArity = ()
Fill var HeapObj.Header.ClosureFilled = ()
Fill var HeapObj.Header.BignumNegative = ()
Fill var HeapObj.Header.BignumWords = ()
