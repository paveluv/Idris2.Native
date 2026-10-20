||| Uses `Mode` by its name and `speed`, never a constructor.
module Pace

import Data.Vect
import Mode

%default total

export
pace : Mode -> Nat
pace m = Mode.speed m + 1

export
lanes : Mode.Lanes
lanes = [1, 2]
