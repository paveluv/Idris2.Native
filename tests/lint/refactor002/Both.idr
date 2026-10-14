||| Names a header and a part: it imports both modules.
module Both

import Heap.Header

%default total

export
partsOfCon : Nat
partsOfCon = sum (map place (parts (Con 1)))
