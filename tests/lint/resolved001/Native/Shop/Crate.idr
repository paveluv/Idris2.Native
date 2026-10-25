||| A type of ours laid out over a kind, its statement made with it, as the
||| representation contract asks; and a statement for a type of `base`
||| (`Bool`), which belongs in `Native.Types.Repr`: reported (`repr-orphan`).
module Native.Shop.Crate

import Native.Types.Kind
import Native.Types.Repr

%default total

export
data Crate : Type where [external]

public export
Only Kind.CON Crate where

public export
Immediate Bool where
