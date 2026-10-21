||| The Idris type of an entry of the contract (`PortTy`): what the runtime's
||| function for a port of the contract (`Native.Port`) must be, so that
||| Idris checks each where the runtime is built; and the Idris type of each
||| carrier (`Carried`), which it is made of. The code generator reads the
||| ports as data and never needs their types, so these are the runtime's:
||| a carrier names the runtime core's `ByteAddr`, which the contract cannot.
module Native.Runtime.PortTy

-- lint: allow public-import: a `PortTy` reduces through the port's reading
-- (`Native.Port`) and its machine types' Idris types (`Mach.type`), which
-- every module that writes one in a signature needs
import public Native.Mach
import public Native.Port

import Native.Runtime.ByteAddr
import Native.Runtime.Ordo

import Native.Carrier
import Native.Flat.Uniform as Flat

%default total

||| The Idris type of a carrier, in a call whose value type is `a`: a
||| machine type's own, a value as ordinary code holds it, of its type or of
||| the call's, and a byte address.
public export
Carried : (0 a : Type) -> Carrier -> Type
Carried _ (Carrier.Machine m) = Mach.type m
Carried _ (Carrier.ValueOf t) = Flat.Uniform t
Carried a Carrier.Value = Flat.Uniform a
Carried _ Carrier.ByteAddr = ByteAddr

||| The Idris type of an entry of the port: an operation on the arguments
||| the port takes, of the result it gives, for any value type `a` if a
||| carrier is a value; erased, and only where a carrier names it, so a
||| caller of an entry that names none has nothing to solve.
public export
PortTy : Port -> Type
PortTy p = forValue (any isValue (carriers p)) (\a => arrows a p.takes)
  where
    carriers : Port -> List Carrier
    carriers q = q.takes ++ maybe [] (\c => [c]) q.gives

    isValue : Carrier -> Bool
    isValue Carrier.Value = True
    isValue _ = False

    -- a value type is quantified only if a carrier names one; otherwise any
    -- will do, unnamed
    forValue : Bool -> ((0 a : Type) -> Type) -> Type
    forValue True f = {0 a : Type} -> f a
    forValue False f = f ()

    result : (0 a : Type) -> Maybe Carrier -> Type
    result _ Nothing = ()
    result a (Just c) = Carried a c

    arrows : (0 a : Type) -> List Carrier -> Type
    arrows a [] = Ordo.Op Ordo (result a p.gives)
    arrows a (c :: cs) = Carried a c -> arrows a cs
