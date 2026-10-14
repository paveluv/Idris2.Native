||| Names only a header: its import stays as it is.
module Dump

import Heap.Header

%default total

export
first : List Header
first = [Con 1]
