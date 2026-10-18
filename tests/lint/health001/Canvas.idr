||| Where the two `area`s meet, written without a namespace: each use is
||| resolved by its argument's type, and each is the area of its shape.
module Canvas

import Circle
import Square

%default total

||| The area of a circle and a square together.
export
canvas : Nat
canvas = area (MkCircle 1) + area (MkSquare 2)
