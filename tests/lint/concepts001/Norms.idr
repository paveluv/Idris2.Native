||| Uses `Point` by a field alone: its concept, not `twice`. One importer:
||| no evidence for `distinction`.
module Norms

import Geo.Point

%default total

export
xOf : Point -> Nat
xOf p = p.x
