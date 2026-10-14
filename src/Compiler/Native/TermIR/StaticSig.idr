||| What a reference knows of a static object (`StaticSig`).
|||
||| Part of the term IR (`Compiler.Native.TermIR.Program` says what it is).
module Compiler.Native.TermIR.StaticSig

import Compiler.Native.HeapObject.Kind
import Core.Name

%default total

||| What a reference knows of a static object.
public export
record StaticSig where
  constructor MkStaticSig
  sym : Name
  kind : Kind
