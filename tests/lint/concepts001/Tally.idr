||| `Tally` imports `Bulk` for one of its four concepts; precision would
||| count the other three, but `Bulk` is left out of it.
module Tally

import Bulk

%default total

||| A tally of one.
export
tally : Nat
tally = one
