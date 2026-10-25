||| The type of a pure load (`PureLoad`): a backend primitive that reads an
||| object (`Native.Primitive` says what a primitive is), defined at the one
||| type it reads.
|||
||| A load is pure where nothing writes what it reads once the value
||| exists: it may then be done at any time, before or after any effect,
||| and its result shared. So the type asks the representation contract,
||| where the reader is declared, that its object's type be a `BYTES` always
||| (`Repr.Only`), which gives the load its object and the payload's place,
||| and immutable (`Repr.Immutable`), which gives it its leave: a reader of
||| a type without both is refused there, `PureLoad Buffer` among them, and
||| the evidence is not made by hand (`forged-instance`). The type's flat
||| layout must be one value as ordinary code holds it, a record of a
||| `Uniform` (`Types.Bytes`), which the native code generator narrows to
||| its object and loads from; this type does not check it, and the flat
||| translation refuses any other.
|||
||| Part of the type layer, the modules of `Types` (`Types.Kind` says what
||| it is).
module Native.Types.PureLoad

import Native.Types.Kind
import Native.Types.Repr

import Native.Primitive

%default total

||| A primitive of the signature that reads a value of `a`: a function of
||| the value, then of the signature's arguments, to its results.
public export
PureLoad : (a : Type) -> {auto 0 only : Repr.Only Kind.BYTES a} ->
           {auto 0 imm : Repr.Immutable a} -> Primitive.Signature -> Type
PureLoad a sig = a -> Primitive.FunctionTy sig
