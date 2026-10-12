||| A shape, and how one shows: the module the others use, each in its own
||| way.
module Shape

%default total

||| A circle by its radius, a square by its side.
public export
data Shape = Circle Nat | Square Nat

export
Show Shape where
  show (Circle r) = "circle " ++ show r
  show (Square s) = "square " ++ show s
