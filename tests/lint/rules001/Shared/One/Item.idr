||| A module of the group `One` under `Shared`. `Spare` has a group `One`
||| too, and nothing is reported: a name is qualified by its module's path,
||| `Shared.One.Item.item` from a module at the top, which says which.
module Shared.One.Item

%default total

||| An item.
export
item : Nat
item = 1
