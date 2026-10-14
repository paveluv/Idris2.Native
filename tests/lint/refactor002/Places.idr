||| Names only a part: it imports `Heap.Part` in place of `Heap.Header`.
module Places

import Heap.Header

%default total

export
tagPlace : Nat
tagPlace = place Tag
