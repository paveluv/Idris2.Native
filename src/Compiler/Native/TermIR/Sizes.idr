||| The parts of a header that alone decide an object's size (`Sizes`), and
||| what fills an object of a run-time size.
|||
||| Part of the term IR (`Compiler.Native.TermIR.Program` says what it is).
module Compiler.Native.TermIR.Sizes

import Compiler.Native.TermIR.Opnd

import Compiler.Native.HeapObject.Enc
import Compiler.Native.HeapObject.Header
import Compiler.Native.HeapObject.Kind
import Compiler.Native.IRCommon.Ty

%default total

||| The parts that alone decide an object's size.
public export
data Sizes : HeaderPart k -> Type where
  SizesArray : Sizes ArrayElems
  SizesString : Sizes StringBytes
  SizesStringChars : Sizes StringChars
  SizesBuffer : Sizes BufferBytes

||| What fills a new object of a run-time size, by the part that sizes it: a
||| `Val` for every element of an `ARRAY`, which the collector scans;
||| nothing for the raw kinds, whose bytes are left as they are. A part that
||| sizes nothing (`Sizes` has no proof for it) takes nothing.
public export
Fill : (Ty enc -> Type) -> HeaderPart k -> Type
Fill var ArrayElems = Opnd var Val
Fill var StringAscii = ()
Fill var StringBytes = ()
Fill var StringChars = ()
Fill var BufferBytes = ()
Fill var ConId = ()
Fill var ConArity = ()
Fill var ClosureArity = ()
Fill var ClosureFilled = ()
Fill var BignumNegative = ()
Fill var BignumWords = ()
