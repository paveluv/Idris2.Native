||| The types of an object's fields, from its header (`fieldTys`) or, where
||| its kind says, from the kind (`cellTy`), and the headers the IR may
||| allocate.
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
fieldTys (Types.Header.ClosureH _ f) = IRCommon.Ty.CodeAddr :: replicate f IRCommon.Ty.Val
fieldTys Types.Header.Int64H = [IRCommon.Ty.W64]
fieldTys Types.Header.DoubleH = [IRCommon.Ty.F64]
fieldTys h@(Types.Header.StringH _ _) = replicate (Types.Header.fieldWords h) IRCommon.Ty.W64
fieldTys h@(Types.Header.StringCharsH _) = replicate (Types.Header.fieldWords h) IRCommon.Ty.W64
fieldTys (Types.Header.BignumH _ n) = replicate n IRCommon.Ty.W64
fieldTys Types.Header.IORefH = [IRCommon.Ty.Val]
fieldTys (Types.Header.ArrayH n) = replicate n IRCommon.Ty.Val
fieldTys (Types.Header.StructH r v) = replicate r IRCommon.Ty.W64 ++ replicate v IRCommon.Ty.Val
fieldTys h@(Types.Header.BufferH _) = replicate (Types.Header.fieldWords h) IRCommon.Ty.W64
fieldTys Types.Header.PtrH = [IRCommon.Ty.W64]

||| The type of the word at a byte offset of an object of the kind, moved by
||| an index or not, where the kind alone says, as `fieldTys` gives it:
||| every field of a constructor, a reference and an array a `Val`, a
||| double's bits an `F64`, every word of the other raw objects a `W64`, a
||| closure's code address at 8 and its arguments after, a continuation's
||| resume address at 0 and its parent at 8. A header is no field: it is
||| read by `LoadHeader`, not loaded. Nothing where the kind does not say:
||| a closure's word at an index, a mutable record's, whose header counts
||| its raw words, a continuation's live words.
public export
cellTy : Types.Kind -> (indexed : Bool) -> (offset : Int) -> Maybe (IRCommon.Ty enc)
cellTy Types.Kind.CON _ _ = Just IRCommon.Ty.Val
cellTy Types.Kind.IOREF _ _ = Just IRCommon.Ty.Val
cellTy Types.Kind.ARRAY _ _ = Just IRCommon.Ty.Val
cellTy Types.Kind.CLOSURE True _ = Nothing
cellTy Types.Kind.CLOSURE False o = Just (if o == 8 then IRCommon.Ty.CodeAddr else IRCommon.Ty.Val)
cellTy Types.Kind.INT64 _ _ = Just IRCommon.Ty.W64
cellTy Types.Kind.DOUBLE _ _ = Just IRCommon.Ty.F64
cellTy Types.Kind.STRING _ _ = Just IRCommon.Ty.W64
cellTy Types.Kind.BIGNUM _ _ = Just IRCommon.Ty.W64
cellTy Types.Kind.STRUCT _ _ = Nothing
cellTy Types.Kind.BUFFER _ _ = Just IRCommon.Ty.W64
cellTy Types.Kind.PTR _ _ = Just IRCommon.Ty.W64
cellTy Types.Kind.CONT True _ = Nothing
cellTy Types.Kind.CONT False o =
  if o == 0 then Just IRCommon.Ty.CodeAddr else if o == 8 then Just IRCommon.Ty.Val else Nothing

||| A header the IR may allocate: its parts fit their bits, and a closure has
||| fewer arguments filled than its arity.
public export
wellFormed : {0 k : Types.Kind} -> Types.Header enc k -> Bool
wellFormed h@(Types.Header.ClosureH arity filled) = Types.Header.fits h && filled < arity
wellFormed h = Types.Header.fits h
