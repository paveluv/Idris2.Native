||| Imports both modules joined, one under the name the joined module has:
||| it imports `Ops`, once, the alias gone.
module Calc

import Ops.Add
import Ops.Sub as Ops

%default total

export
calc : Nat
calc = Ops.sub (add 2 3) 1
