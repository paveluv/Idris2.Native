||| Uses `Mode` by its name and `speed`, never a constructor.
module Pace

import Data.Vect
import Mode

%default total

export
pace : Mode -> Nat
pace m = speed m + 1

export
lanes : Lanes
lanes = [1, 2]
