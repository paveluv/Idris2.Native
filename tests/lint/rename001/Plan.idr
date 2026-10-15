||| An importer of the renamed module: it imports `New.Item`, and a name
||| written by the old name's last parts is written by as many of the new
||| one's: `Thing.width` is `Item.width`, `Old.Thing.width` is
||| `New.Item.width`.
module Plan

import Old.Thing

%default total

export
twice : Nat
twice = Thing.width + Old.Thing.width
