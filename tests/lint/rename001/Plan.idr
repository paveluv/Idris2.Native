||| An importer of the renamed module: it imports `Item`, and a name written
||| by the old name's last parts is written by as many of the new one's, all
||| of them where it has fewer: `Thing.width` and `Old.Thing.width` are both
||| `Item.width`.
module Plan

import Old.Thing

%default total

export
twice : Nat
twice = Thing.width + Old.Thing.width
