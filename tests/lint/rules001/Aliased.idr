||| Qualifiers otherwise than the module's path from here: `Shared.One.Item`
||| imported as `Wrong`, where an alias is its key type's qualifier,
||| `Shared.One`; and `One.Piece.piece`, where the path from a module at
||| the top is the whole name, `Spare.One.Piece.piece`; and `Wrong.item`,
||| under the wrong alias. `import-alias`, three times.
module Aliased

import Shared.One.Item as Wrong
import Spare.One.Piece

%default total

||| An item and a piece.
export
both : Nat
both = Wrong.item + One.Piece.piece
