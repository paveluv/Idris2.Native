||| What a reference knows of a static object (`StaticSig`).
|||
||| Part of the term IR (`Compiler.Native.TermIR.Program` says what it is).
module Compiler.Native.TermIR.StaticSig

import Core.Name
import HeapObj.Kind as HeapObj

%default total

||| What a reference knows of a static object.
public export
record StaticSig where
  constructor MkStaticSig
  sym : Name
  kind : HeapObj.Kind
