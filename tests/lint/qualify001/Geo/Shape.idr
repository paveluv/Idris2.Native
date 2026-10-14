||| A type, its constructors and a function about it.
module Geo.Shape

%default total

||| A shape.
public export
data Shape = Circle Nat | Square Nat

||| The area of a shape, roughly.
export
area : Shape -> Nat
area (Circle r) = 3 * r * r
area (Square s) = s * s

||| A name the Prelude has too: whoever writes `length` means one or the
||| other, and only the type checker knows which.
export
length : Shape -> Nat
length (Circle r) = 2 * r
length (Square s) = s
