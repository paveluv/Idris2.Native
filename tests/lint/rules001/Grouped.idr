||| Names qualified as they should be, with their module's path from here,
||| a module at the top, so the whole name: `Shared.One.Item.item`; and the
||| key type, named after its module, `Shared.One.Item`, under the alias
||| its qualifier is. No finding.
module Grouped

import Shared.One.Item as Shared.One

%default total

||| The item.
export
the1 : Nat
the1 = Shared.One.Item.item
