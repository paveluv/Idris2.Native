||| The Idris type of an entry of the contract (`PortTy`): what the runtime's
||| function for a port of the contract (`Native.Port`) must be, so that
||| Idris checks each where the runtime is built. The code generator reads
||| the ports as data and never needs their types, so this is the runtime's.
module Native.Runtime.PortTy

import Native.Runtime.Heap

import Native.Flat.Uniform as Flat
import Native.HeapObj.Shape as HeapObj
import Native.Port

%default total

||| The Idris type of an entry of the port, for a side whose addresses are
||| `addr`: an operation on the arguments the port takes, of the result it
||| gives, for any shape `s` if a carrier is an address, and any value type
||| `a` if one is a value; erased, and only where a carrier names them, so a
||| caller of an entry that names neither has nothing to solve.
public export
PortTy : (addr : (0 s : HeapObj.Shape) -> Type) -> Port -> Type
PortTy addr p =
  forShape (any isAddress (carriers p)) (\s => forValue (any isValue (carriers p)) (\a => arrows s a p.takes))
  where
    carriers : Port -> List Port.Carrier
    carriers q = q.takes ++ maybe [] (\c => [c]) q.gives

    isAddress : Port.Carrier -> Bool
    isAddress Port.Address = True
    isAddress _ = False

    isValue : Port.Carrier -> Bool
    isValue Port.Value = True
    isValue _ = False

    -- a shape is quantified only if a carrier names one; otherwise any will
    -- do, unnamed
    forShape : Bool -> ((0 s : HeapObj.Shape) -> Type) -> Type
    forShape True f = {0 s : HeapObj.Shape} -> f s
    forShape False f = f HeapObj.Shape.VALUES

    forValue : Bool -> ((0 a : Type) -> Type) -> Type
    forValue True f = {0 a : Type} -> f a
    forValue False f = f ()

    carried : (0 s : HeapObj.Shape) -> (0 a : Type) -> Port.Carrier -> Type
    carried _ _ Port.Word = Bits64
    carried _ _ Port.Signed = Int
    carried _ _ (Port.ValueOf t) = Flat.Uniform t
    carried _ a Port.Value = Flat.Uniform a
    carried s _ Port.Address = addr s

    result : (0 s : HeapObj.Shape) -> (0 a : Type) -> Maybe Port.Carrier -> Type
    result _ _ Nothing = ()
    result s a (Just c) = carried s a c

    arrows : (0 s : HeapObj.Shape) -> (0 a : Type) -> List Port.Carrier -> Type
    arrows s a [] = Heap.Op Heap (result s a p.gives)
    arrows s a (c :: cs) = carried s a c -> arrows s a cs

||| The Idris type of an `%extern` of the port: no extern carries an
||| address, the type of which is the memory module's, so one that would is
||| not inhabited.
public export
ExternTy : Port -> Type
ExternTy = PortTy (\_ => Void)
