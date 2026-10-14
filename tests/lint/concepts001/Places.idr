||| Uses `Part` alone, apart from every user of `Header`.
module Places

import Heap.Header

%default total

export
tagPlace : Nat
tagPlace = place Tag
