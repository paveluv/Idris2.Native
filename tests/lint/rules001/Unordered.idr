||| Imports out of order: a private import before the public one. The first
||| import out of its place is reported, with the one that belongs there.
module Unordered

import Data.String
import public Data.List
import Data.Maybe

%default total
