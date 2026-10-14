||| Leaving a module out of a component of the score, wrongly: `exclusion`.
||| The first comment names a component that leaves no modules out, and the
||| second gives no reason; each is reported. (A module rightly left out of
||| precision is in the score's fixtures, `concepts001/Bulk.idr`.)
module Excludes

-- lint: exclude cohesion: no component but precision leaves modules out

-- lint: exclude precision:

%default total
