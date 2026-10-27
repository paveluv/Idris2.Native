||| A module that uses another module's `allNames` (`Roster`'s), not
||| Idris's, which decodes nothing: not reported (`decoding-walk`), since
||| the rule reports the name only in a module that uses Idris's.
module Census

import Roster

%default total

export
censusSize : Nat
censusSize = length Roster.allNames
