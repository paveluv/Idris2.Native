||| What `order-imports` changes: the public imports first, then the private
||| ones, each alphabetical.
module Imports

import Data.String
import public Data.Maybe
import Data.List

%default total

export
joined : List String -> String
joined = fastConcat . intersperse ", " . map trim . catMaybes . map Just
