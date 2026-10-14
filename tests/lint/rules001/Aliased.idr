||| Qualifiers that are not groups: `Shared.One.Item` imported as `Wrong`,
||| where an alias is the module's group, `One`; and `One.Piece.piece`,
||| qualified by a group and a module, where its module imported as its
||| group gives `One.piece`. `import-alias`, twice.
module Aliased

import Shared.One.Item as Wrong
import Spare.One.Piece

%default total

||| An item and a piece.
export
both : Nat
both = Wrong.item + One.Piece.piece
