||| A static object's definition (`StaticDef`), and the words it holds.
|||
||| Part of the term IR (`Compiler.Native.TermIR.Program` says what it is).
module Compiler.Native.TermIR.StaticDef

import Compiler.Native.TermIR.Decls
import Compiler.Native.TermIR.FieldTys
import Compiler.Native.TermIR.Sig
import Compiler.Native.TermIR.StaticSig
import Compiler.Native.TermIR.Var

import Compiler.Native.HeapObject.Enc as HeapObject
import Compiler.Native.HeapObject.Header as HeapObject
import Compiler.Native.HeapObject.Kind as HeapObject
import Compiler.Native.IRCommon.Conv
import Compiler.Native.IRCommon.Ty as IRCommon
import Core.Name
import Data.So
import Data.Vect

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
  MkStaticDef : {0 d : Decls enc} -> {k : HeapObject.Kind} -> (h : HeapObject.Header enc k) -> {auto 0 ok : So (wellFormed h)} ->
                Vect (fieldWords h) (SField d) -> StaticDef d (StaticSig.MkStaticSig s k)
