||| A module that writes the shorthand without importing what it names:
||| after `inline-alias` it writes `Store.Tag.Tag String Nat`, the type's
||| module by its path from here, and imports `Store.Tag`.
module Plan

import Store.Named

%default total

export
labels : List (Store.Named.Named Nat) -> Nat
labels xs = length xs
