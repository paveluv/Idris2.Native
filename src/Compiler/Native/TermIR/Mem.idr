||| The term IR's memory references (`Mem`).
|||
||| Part of the term IR (`Compiler.Native.TermIR.Program` says what it is).
module Compiler.Native.TermIR.Mem

import Compiler.Native.TermIR.Opnd

import Compiler.Native.HeapObject.Enc
import Compiler.Native.HeapObject.Kind
import Compiler.Native.IRCommon.Ty

%default total

||| A memory reference's base: an object pointer or a raw address, never a
||| `Val`, which may be a fixnum.
public export
data Base : (var : Ty enc -> Type) -> Type where
  AtWord : Opnd var W64 -> Base var
  AtPtr : Opnd var (PtrTo k) -> Base var

||| A memory reference: a base, an optional index counting units of the
||| access's width, and a constant byte offset.
public export
record Mem {0 enc : Enc} (var : Ty enc -> Type) where
  constructor MkMem
  base : Base var
  index : Maybe (Opnd var W64)
  offset : Int

public export
traverseMem : Applicative f => ({0 t : Ty enc} -> Opnd v t -> f (Opnd w t)) -> Mem v -> f (Mem w)
traverseMem g (MkMem (AtWord b) i o) = [| (\b', i' => MkMem (AtWord b') i' o) (g b) (traverse g i) |]
traverseMem g (MkMem (AtPtr b) i o) = [| (\b', i' => MkMem (AtPtr b') i' o) (g b) (traverse g i) |]
