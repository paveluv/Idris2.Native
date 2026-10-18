||| `Kept` imports `Data.List` and uses nothing of it, as `Spare` does, and
||| says why: the suppression covers the finding. Without the resolution,
||| when a TTC is stale, the rule does not run, and the suppression, which
||| then suppresses nothing, is not reported for it.
module Kept

-- lint: allow import-unused: a fixture's import, kept to be suppressed
import Data.List

%default total

||| A number of no list.
export
kept : Nat
kept = 3
