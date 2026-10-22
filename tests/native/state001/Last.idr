||| The runtime's state is the words of the area `RUNTIME`, each a named
||| field of the carrier it holds. Its last word, why the last OS service
||| failed, is a count: `get "lastFailure"` reads it as a `Bits64`, which
||| Idris finds from its name where this is compiled.
module Last

import Native.Carrier
import Native.Field
import Native.Mach
import Native.Runtime.Cell
import Native.Runtime.Ordo
import Native.Runtime.PortTy
import Native.Runtime.State

%default total

-- a count, so a `Bits64`
lastFailure : Op Ordo Bits64
lastFailure = State.get "lastFailure"
