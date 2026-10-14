||| Uses `Part` and `wordBits` together, so the two are one piece of
||| `Heap.Header`, and `Header` the other.
module Bits

import Heap.Glued
import Heap.Header

%default total

export
countBits : Nat
countBits = minus wordBits (spanOf (place Count))
