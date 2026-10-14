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

||| The sides a shape has: about the module's type. Not reported.
export
sides : Shape -> Nat
sides (Circle _) = 0
sides (Square _) = 4

||| Two to a power: its type and body name nothing of ours, and it is
||| exported from a module about a type. A reader looking for it would not
||| look here: `generic-export`.
export
pow2 : Nat -> Nat
pow2 Z = 1
pow2 (S n) = 2 * pow2 n

||| A constant: a fact of its module, whatever its type. Not reported.
export
unit : Nat
unit = 1

||| A name the module gives a shape: its type names nothing of ours, but it
||| writes a string, which names something, so it is a fact of the module.
||| Not reported.
export
tag : Nat -> String
tag n = "shape-" ++ show n
