||| An implementation built from an interface's constructor, which no search
||| vouches for: reported (`forged-instance`), whatever the interface. The
||| constructor is reached by its qualified name, the only way it lexes as
||| one name.
module Forged

%default total

interface Marked a where

0 marked : Marked Nat
marked = Forged.__mkMarked
