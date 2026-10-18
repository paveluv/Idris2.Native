||| A module that imports `Token` under an alias, and writes its names
||| with it: renamed, the alias kept.
module Aliased

import Token as T

%default total

fresh : T.Tok
fresh = T.MkTok
