||| A module that keeps every rule: its imports in order, the public ones
||| first, then the private ones, each alphabetical as a reader sorts, and a
||| `%default`. Its public imports are not those of a façade, so they say
||| why, in a suppression whose paragraph covers both. A finding here would
||| be the linter's mistake.
module Ordered

-- lint: allow public-import: the users of `size` take its lists and maybes
import public Data.List
import public Data.Maybe

import Data.So
import Data.String

%default total

||| The length of a list.
export
size : List a -> Nat
size = length
