||| A static object's definition (`StaticDef`), and the words it holds.
|||
||| Part of the term IR (`Native.Codegen.TermIR.Program` says what it is).
module Native.Codegen.TermIR.StaticDef

import Native.Codegen.TermIR.Decls
import Native.Codegen.TermIR.FieldTys
import Native.Codegen.TermIR.Sig
import Native.Codegen.TermIR.StaticSig
import Native.Codegen.TermIR.Var

import Core.Name
import Data.List
import Data.List.Quantifiers
import Data.So
import Data.Vect
import Native.Codegen.IRCommon.Conv
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.HeapObj.Shape as HeapObj
import Native.HeapObj.ValEnc
import Native.Types.Enc as Types
import Native.Types.Header as Types
import Native.Types.Kind as Types

%default total

||| The types of the fields a raw word fills: a word, and a double, which a
||| static holds as its bits.
public export
data IsBits : IRCommon.Ty enc -> Type where
  BitsW : IsBits IRCommon.Ty.W64
  BitsF : IsBits IRCommon.Ty.F64

||| A word of a static object, of the type of the field it fills, as an
||| allocated object's operands are: a uniform value's forms fill a `Val`,
||| a function's entry a closure's code, a raw word a word or a double.
public export
data SField : Decls enc -> IRCommon.Ty enc -> Type where
  ||| A raw word, as it is.
  SWord : {auto 0 bits : IsBits t} -> Int64 -> SField d t
  ||| A uniform value that is a fixnum, whose word the value encoding gives.
  ||| The erased value is `SVal 0`, as the erased operand is fixnum 0.
  SVal : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} ->
         (i : Int64) -> {auto 0 ok : So (HeapObj.ValEnc.inFixnumRange (cast i))} ->
         SField {enc} d IRCommon.Ty.Val
  ||| The address of another static, as a pointer word.
  SRef : Var d.statics s -> SField d IRCommon.Ty.Val
  ||| The entry address of a CPS function: a static closure's code.
  SCode : Var d.sigs (MkSig n IRCommon.Conv.CPS ps cv) -> SField d IRCommon.Ty.CodeAddr

||| The fields of a static of words, each word as it is, by its header's
||| counts (`Header.counts`), of words or of bytes: a string's, a big
||| integer's, a run of bytes'. They are the header's fields (`fieldTys`)
||| where its kind's raw words are words (`Kind.rawRep`), and they need
||| only the counts, so a header known only by its kind, as a string
||| literal's is, has them.
export
wordFields : (c : HeapObj.Shape.Counts HeapObj.Shape.RAW) ->
             Vect (HeapObj.Shape.fieldWords c) Int64 ->
             All (SField d) (FieldTys.countsTys IRCommon.Ty.W64 c)
wordFields c ws = case c of
  HeapObj.Shape.BytesOf _ => wordRun ws
  HeapObj.Shape.WordsOf _ => wordRun ws
  where
    -- a run of fields that are words, each word as it is
    wordRun : Vect n Int64 -> All (SField d) (Data.List.replicate n IRCommon.Ty.W64)
    wordRun [] = []
    wordRun (w :: rest) = SWord w :: wordRun rest

||| A static object's definition: its header, and after it a word of each
||| field's type (`fieldTys`).
public export
data StaticDef : Decls enc -> StaticSig -> Type where
  MkStaticDef : {0 d : Decls enc} -> {k : Types.Kind} -> (h : Types.Header enc k) ->
                {auto 0 ok : So (wellFormed h)} ->
                All (SField d) (fieldTys h) -> StaticDef d (MkStaticSig s k)
