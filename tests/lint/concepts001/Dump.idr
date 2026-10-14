||| Uses `Header` only by showing one, an implementation found by search:
||| one of `Heap.Header`'s three concepts.
module Dump

import Heap.Header
import Heap.Left
import Heap.Right
import Ops.Add
import Ops.Sub

%default total

export
dump : Header -> String
dump h = show h ++ show (sub (add left right) 0)
