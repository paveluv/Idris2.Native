||| The shape of an entry of the contract (`Port`): what each register of a
||| call across it carries, as data, and the Idris type that says
||| (`PortTy`).
|||
||| The contract's entries are the runtime's routines, which generated code
||| calls, the inline externs, which the lowering provides to the runtime's
||| code, and the OS services, which a platform provides to the rest of the
||| runtime (`Native.Routines`, `Native.Intrinsics`, `Native.Services`). Each
||| is a field of a record whose type is its port: the side that provides
||| an entry gives a value of the port's Idris type, which Idris checks where
||| that side is built; the code generator reads the registers of a call
||| from the port, the same data. Neither restates the other.
|||
||| Part of the contract between compiled code and the runtime, with the
||| heap-object model (`HeapObj.Enc` says what it is).
module Native.Port

import Native.Flat.Uniform as Flat
import Native.Heap
import Native.HeapObj.Kind as HeapObj

%default total

||| What a register carries across the boundary, as the Idris type it is.
public export
data Carrier
  = ||| A word: `Bits64`.
    Word
  | ||| A signed word: `Int`.
    Signed
  | ||| A value of the type, as ordinary code holds it: `Uniform t`.
    ValueOf Type
  | ||| Any value, as ordinary code holds it: `Uniform a`, for the call's `a`.
    Value
  | ||| The address of an object of the call's kind `k`, as the side that
    ||| gives the entry types addresses: `addr k`.
    Address

||| An entry's shape: what its arguments carry, in order, and what its
||| result does, if it has one. Every entry takes the token too, last, and
||| returns it with the result: it is an operation (`Op`).
public export
record Port where
  constructor MkPort
  takes : List Carrier
  gives : Maybe Carrier

||| The Idris type of an entry of the port, for a side whose addresses are
||| `addr`: an operation on the arguments the port takes, of the result it
||| gives, for any kind `k` and any value type `a` the carriers name.
public export
PortTy : (addr : HeapObj.Kind -> Type) -> Port -> Type
PortTy addr p = {k : HeapObj.Kind} -> {a : Type} -> arrows k a p.takes
  where
    carried : (k : HeapObj.Kind) -> (a : Type) -> Carrier -> Type
    carried _ _ Word = Bits64
    carried _ _ Signed = Int
    carried _ _ (ValueOf t) = Flat.Uniform t
    carried _ a Value = Flat.Uniform a
    carried k _ Address = addr k

    result : (k : HeapObj.Kind) -> (a : Type) -> Maybe Carrier -> Type
    result _ _ Nothing = ()
    result k a (Just c) = carried k a c

    arrows : (k : HeapObj.Kind) -> (a : Type) -> List Carrier -> Type
    arrows k a [] = Heap.Op Heap (result k a p.gives)
    arrows k a (c :: cs) = carried k a c -> arrows k a cs

||| The Idris type of an `%extern` of the port: no extern carries an
||| address, the type of which is the runtime's, so one that would is not
||| inhabited.
public export
ExternTy : Port -> Type
ExternTy = PortTy (\_ => Void)
