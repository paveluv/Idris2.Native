||| `Tally` imports `Bulk` for one of its three names; precision would count
||| the other two, but `Bulk` is left out of it.
module Tally

import Bulk

%default total

||| A tally of one.
export
tally : Nat
tally = one
