||| A module named almost after its exported type, the type's name beginning
||| the module's: `module-type`, since a reader looks `Rect` up in
||| `Rect.idr`. (Its private `Corner` begins nothing and is not reported.)
module Rectangle

%default total

||| A rectangle.
public export
record Rect where
  constructor MkRect
  width, height : Nat

record Corner where
  constructor MkCorner
  x, y : Nat

||| The rectangle's area.
export
area : Rect -> Nat
area r = r.width * r.height
