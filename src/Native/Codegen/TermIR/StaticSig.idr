||| What a reference knows of a static object (`StaticSig`).
|||
||| Part of the term IR (`Native.Codegen.TermIR.Program` says what it is).
module Native.Codegen.TermIR.StaticSig

import Core.Name
import Native.Types.Kind as Types

%default total

||| What a reference knows of a static object.
public export
record StaticSig where
  constructor MkStaticSig
  sym : Name
  kind : Types.Kind
