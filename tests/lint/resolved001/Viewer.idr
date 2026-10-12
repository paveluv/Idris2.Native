||| `Viewer` reaches `Shape` through the façade `Shapes`, and `Data.Fin`
||| (`FZ`) through `Data.Vect`, a package's module that re-exports it: what
||| a package re-exports is its own design. No finding.
module Viewer

import Data.Vect
import Shapes

%default total

||| One square, in a vector of one.
export
viewer : Vect 1 Shape
viewer = [Square 4]

||| The vector's only position.
export
first : Fin 1
first = FZ
