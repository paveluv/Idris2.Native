||| Levels and positions in a list that grows at its front, as a context
||| does: a position counts from the front, so a new entry moves every
||| entry's; a level counts from the back, so an entry keeps its level as
||| the list grows. In a list of `depth` entries the entry at level `n` is
||| at position `depth - 1 - n` (`position`), and the rule is its own
||| inverse (`level`); either is below `depth` for an `n` below it.
module Native.Data.Level

%default total

||| The position of the entry at the level, in a list of `depth` entries.
export
position : (depth, level : Nat) -> Nat
position depth l = minus depth (S l)

||| The level of the entry at the position, in a list of `depth` entries:
||| the same rule.
export
level : (depth, position : Nat) -> Nat
level = position
