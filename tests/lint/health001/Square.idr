||| A square and its area: see `Circle`.
module Square

%default total

||| A square, by its side.
public export
data Square = MkSquare Nat

namespace Square
  ||| A square's area.
  export
  area : Square -> Nat
  area (MkSquare s) = s * s
