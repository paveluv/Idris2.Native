||| `Spare` imports `Data.List` and uses nothing of it, nor of what it
||| re-exports: `import-unused`.
module Spare

import Data.List

%default total

||| A number of no list.
export
spare : Nat
spare = 2
