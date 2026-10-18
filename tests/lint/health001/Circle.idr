||| A circle and its area, in a namespace named after its type; a square has
||| its own (`Square`). The two `area`s meet bare in `Canvas`, but each is an
||| overload of its type, one concept across types: not counted against
||| the uniqueness.
module Circle

%default total

||| A circle, by its radius.
public export
data Circle = MkCircle Nat

namespace Circle
  ||| A circle's area, roughly.
  export
  area : Circle -> Nat
  area (MkCircle r) = 3 * r * r
