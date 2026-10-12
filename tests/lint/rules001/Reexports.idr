||| A module that declares something and re-exports an import: a module that
||| uses `Data.List` should import it itself, so the public import is
||| reported.
module Reexports

import public Data.List

%default total

||| A list of one.
export
one : a -> List a
one x = [x]
