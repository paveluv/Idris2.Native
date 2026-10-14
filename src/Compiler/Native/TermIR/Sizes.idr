||| The parts of a header that alone decide an object's size (`Sizes`), and
||| what fills an object of a run-time size.
|||
||| Part of the term IR (`Compiler.Native.TermIR.Program` says what it is).
module Compiler.Native.TermIR.Sizes

import Compiler.Native.TermIR.Opnd

import Compiler.Native.HeapObject.Enc as HeapObject
import Compiler.Native.HeapObject.Header
import Compiler.Native.HeapObject.Kind as HeapObject
import Compiler.Native.IRCommon.Ty as IRCommon

%default total

||| The parts that alone decide an object's size.
public export
data Sizes : HeapObject.Header.HeaderPart k -> Type where
  SizesArray : Sizes HeapObject.Header.ArrayElems
  SizesString : Sizes HeapObject.Header.StringBytes
  SizesStringChars : Sizes HeapObject.Header.StringChars
  SizesBuffer : Sizes HeapObject.Header.BufferBytes

||| What fills a new object of a run-time size, by the part that sizes it: a
||| `Val` for every element of an `ARRAY`, which the collector scans;
||| nothing for the raw kinds, whose bytes are left as they are. A part that
||| sizes nothing (`Sizes` has no proof for it) takes nothing.
public export
Fill : (IRCommon.Ty enc -> Type) -> HeapObject.Header.HeaderPart k -> Type
Fill var HeapObject.Header.ArrayElems = Opnd var IRCommon.Ty.Val
Fill var HeapObject.Header.StringAscii = ()
Fill var HeapObject.Header.StringBytes = ()
Fill var HeapObject.Header.StringChars = ()
Fill var HeapObject.Header.BufferBytes = ()
Fill var HeapObject.Header.ConId = ()
Fill var HeapObject.Header.ConArity = ()
Fill var HeapObject.Header.ClosureArity = ()
Fill var HeapObject.Header.ClosureFilled = ()
Fill var HeapObject.Header.BignumNegative = ()
Fill var HeapObject.Header.BignumWords = ()
