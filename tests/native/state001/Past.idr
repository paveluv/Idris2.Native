||| A name the state does not have: no word is found for it, so it does not
||| typecheck, and no code reads a word of the area the state has not named.
module Past

import Native.Carrier
import Native.Field
import Native.Mach
import Native.Runtime.Cell
import Native.Runtime.Ordo
import Native.Runtime.PortTy
import Native.Runtime.State

%default total

-- the state has no word of this name
pastWord : Op Ordo Bits64
pastWord = State.get "pastTheEnd"
