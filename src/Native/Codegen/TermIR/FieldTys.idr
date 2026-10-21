||| The types of an object's fields, from its header (`fieldTys`) or, where
||| its kind says, from the kind (`cellTy`), and the headers the IR may
||| allocate.
|||
||| Part of the term IR (`Native.Codegen.TermIR.Program` says what it is).
module Native.Codegen.TermIR.FieldTys

import Data.List
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.HeapObj.Shape as HeapObj
import Native.Types.Enc as Types
import Native.Types.Header as Types
import Native.Types.Kind as Types

%default total

||| The types of an object's fields, from its header's counts: the values
||| `Val`s, the raw words of the kind's raw rep (`Kind.rawRep`), a double's
||| bits, a closure's code, a word. So the fields the collector scans
||| (`Header.scanned`) and those the IR treats as GC-visible are the same
||| by construction.
public export
fieldTys : {enc : Types.Enc} -> {k : Types.Kind} -> Types.Header enc k -> List (IRCommon.Ty enc)
fieldTys h = fields (IRCommon.Ty.plain (Types.Kind.rawRep k)) (Types.Header.counts h)
  where
    fields : IRCommon.Ty enc -> HeapObj.Shape.Counts s -> List (IRCommon.Ty enc)
    fields _ (HeapObj.Shape.ValuesOf n) = replicate n IRCommon.Ty.Val
    fields r (HeapObj.Shape.MixedOf raws n) = replicate raws r ++ replicate n IRCommon.Ty.Val
    fields r (HeapObj.Shape.WordsOf n) = replicate n r
    fields r c@(HeapObj.Shape.BytesOf _) = replicate (HeapObj.Shape.fieldWords c) r

||| The type of the word at a byte offset of an object of the kind, moved by
||| an index or not, where the kind alone says, as `fieldTys` gives it: every
||| field of a kind whose fields are values a `Val`, every word of a raw
||| kind its raw rep's, a closure's code address at 8 and its arguments
||| after, a continuation's resume address at 0 and its parent at 8. A header
||| is no field: it is read by `LoadHeader`, not loaded. Nothing where the
||| kind does not say: a closure's word at an index, a mutable record's,
||| whose header counts its raw words, a continuation's live words.
public export
cellTy : Types.Kind -> (indexed : Bool) -> (offset : Int) -> Maybe (IRCommon.Ty enc)
cellTy Types.Kind.CLOSURE True _ = Nothing
cellTy Types.Kind.CLOSURE False o =
  Just
    (if o == 8 then IRCommon.Ty.plain (Types.Kind.rawRep Types.Kind.CLOSURE) else IRCommon.Ty.Val)
cellTy Types.Kind.STRUCT _ _ = Nothing
cellTy Types.Kind.CONT True _ = Nothing
cellTy Types.Kind.CONT False o =
  if o == 0 then Just IRCommon.Ty.CodeAddr else if o == 8 then Just IRCommon.Ty.Val else Nothing
cellTy k _ _ = case Types.Kind.shape k of
  Just HeapObj.Shape.VALUES => Just IRCommon.Ty.Val
  Just HeapObj.Shape.RAW => Just (IRCommon.Ty.plain (Types.Kind.rawRep k))
  _ => Nothing

||| A header the IR may allocate: its parts fit their bits, and a closure has
||| fewer arguments filled than its arity.
public export
wellFormed : {enc : Types.Enc} -> {0 k : Types.Kind} -> Types.Header enc k -> Bool
wellFormed h@(Types.Header.ClosureH arity filled) = Types.Header.fits h && filled < arity
wellFormed h = Types.Header.fits h
