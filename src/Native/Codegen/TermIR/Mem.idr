||| The term IR's memory references (`Mem`).
|||
||| Part of the term IR (`Native.Codegen.TermIR.Program` says what it is).
module Native.Codegen.TermIR.Mem

import Native.Codegen.TermIR.Opnd

import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Types.Enc as Types
import Native.Types.Kind as Types

%default total

||| A memory reference's base: an object pointer or a raw address, never a
||| `Val`, which may be a fixnum.
public export
data Base : (var : IRCommon.Ty enc -> Type) -> Type where
  AtWord : Opnd var IRCommon.Ty.W64 -> Base var
  AtPtr : Opnd var (IRCommon.Ty.PtrTo k) -> Base var

||| A memory reference: a base, an optional index counting units of the
||| access's width, and a constant byte offset.
public export
record Mem {0 enc : Types.Enc} (var : IRCommon.Ty enc -> Type) where
  constructor MkMem
  base : Base var
  index : Maybe (Opnd var IRCommon.Ty.W64)
  offset : Int

public export
traverseMem : Applicative f => ({0 t : IRCommon.Ty enc} -> Opnd v t -> f (Opnd w t)) -> Mem v ->
              f (Mem w)
traverseMem g (MkMem (AtWord b) i o) =
  [| (\b', i' => MkMem (AtWord b') i' o) (g b) (traverse g i) |]
traverseMem g (MkMem (AtPtr b) i o) = [| (\b', i' => MkMem (AtPtr b') i' o) (g b) (traverse g i) |]
