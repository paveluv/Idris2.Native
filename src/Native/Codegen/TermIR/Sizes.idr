||| The parts of a header that alone decide an object's size (`Sizes`), and
||| what fills an object of a run-time size.
|||
||| Part of the term IR (`Native.Codegen.TermIR.Program` says what it is).
module Native.Codegen.TermIR.Sizes

import Native.Codegen.TermIR.Opnd

import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Types.Enc as Types
import Native.Types.Header
import Native.Types.Kind as Types

%default total

||| The parts that alone decide an object's size.
public export
data Sizes : Types.Header.HeaderPart k -> Type where
  SizesArray : Sizes Types.Header.ArrayElems
  SizesString : Sizes Types.Header.StringBytes
  SizesStringChars : Sizes Types.Header.StringChars
  SizesBuffer : Sizes Types.Header.BufferBytes

||| What fills a new object of a run-time size, by the part that sizes it: a
||| `Val` for every element of an `ARRAY`, which the collector scans;
||| nothing for the raw kinds, whose bytes are left as they are. A part that
||| sizes nothing (`Sizes` has no proof for it) takes nothing.
public export
Fill : (IRCommon.Ty enc -> Type) -> Types.Header.HeaderPart k -> Type
Fill var Types.Header.ArrayElems = Opnd var IRCommon.Ty.Val
Fill var Types.Header.StringAscii = ()
Fill var Types.Header.StringBytes = ()
Fill var Types.Header.StringChars = ()
Fill var Types.Header.BufferBytes = ()
Fill var Types.Header.ConId = ()
Fill var Types.Header.ConArity = ()
Fill var Types.Header.ClosureArity = ()
Fill var Types.Header.ClosureFilled = ()
Fill var Types.Header.BignumNegative = ()
Fill var Types.Header.BignumWords = ()
Fill var Types.Header.StructRaws = ()
Fill var Types.Header.StructValues = ()
