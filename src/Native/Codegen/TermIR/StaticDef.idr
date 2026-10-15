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
import Data.So
import Data.Vect
import Native.Codegen.IRCommon.Conv
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.HeapObj.Enc as HeapObj
import Native.HeapObj.Header as HeapObj
import Native.HeapObj.Kind as HeapObj

%default total

||| A word of a static object.
public export
data SField : Decls enc -> Type where
  SWord : Int64 -> SField d
  SRef : Var d.statics s -> SField d
  SCode : Var d.sigs (Sig.MkSig n IRCommon.Conv.CPS ps cv) -> SField d

||| A static object's definition: its header and its words after it.
public export
data StaticDef : Decls enc -> StaticSig -> Type where
  MkStaticDef : {0 d : Decls enc} -> {k : HeapObj.Kind} -> (h : HeapObj.Header enc k) ->
                {auto 0 ok : So (wellFormed h)} ->
                Vect (fieldWords h) (SField d) -> StaticDef d (StaticSig.MkStaticSig s k)
