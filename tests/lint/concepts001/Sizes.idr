||| Uses `Header` by a constructor and `size`: still the one concept.
module Sizes

import Heap.Header
import Heap.Left
import Heap.Right
import Ops.Add
import Ops.Sub

%default total

export
conSize : Nat
conSize = sub (add (size (Con 3)) (left + right)) 0
