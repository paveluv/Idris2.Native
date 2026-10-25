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
  SizesArray : Sizes Types.Header.ArrayElemsP
  SizesString : Sizes Types.Header.StringBytesP
  SizesStringChars : Sizes Types.Header.StringCharsP
  SizesBytes : Sizes Types.Header.BytesLengthP

||| What fills a new object of a run-time size, by the part that sizes it: a
||| `Val` for every element of an `ARRAY`, which the collector scans;
||| nothing for the raw kinds, whose bytes are left as they are. A part that
||| sizes nothing (`Sizes` has no proof for it) takes nothing.
public export
Fill : (IRCommon.Ty enc -> Type) -> Types.Header.HeaderPart k -> Type
Fill var Types.Header.ArrayElemsP = Opnd var IRCommon.Ty.Val
Fill var Types.Header.StringAsciiP = ()
Fill var Types.Header.StringBytesP = ()
Fill var Types.Header.StringCharsP = ()
Fill var Types.Header.BytesLengthP = ()
Fill var Types.Header.ConIdP = ()
Fill var Types.Header.ConArityP = ()
Fill var Types.Header.ClosureArityP = ()
Fill var Types.Header.ClosureFilledP = ()
Fill var Types.Header.BignumNegativeP = ()
Fill var Types.Header.BignumWordsP = ()
Fill var Types.Header.StructRawsP = ()
Fill var Types.Header.StructValuesP = ()
