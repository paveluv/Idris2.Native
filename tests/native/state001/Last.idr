||| The runtime's state is the words of the area `RUNTIME`, `runtimeWords` of
||| them (32), and each word it names carries a proof that the area holds
||| it. Its last word, 31, is in the area, so naming it checks.
module Last

import Native.Runtime.State

%default total

-- `count 31` asks for `31 < 32 = True`, which Idris proves by computing it
lastWord : State Bits64
lastWord = count 31

-- two words from the 30th end at the area's end: `30 + 2 <= 32 = True`
lastTwo : Bits64
lastTwo = words 30 2
