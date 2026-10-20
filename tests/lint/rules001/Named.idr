||| Functions named with Of after what they give: `of-name` for `sizeOf`, at
||| the top, for `halfOf`, in a `where` block, and for the field `widthOf`;
||| a suppression of it is not taken. A function named for what it gives
||| (`area`), a compound of its argument and result (`boxArea`), and a
||| constructor whose Of introduces its argument (`SizeOf`) give none.
module Named

%default total

public export
data Measure = SizeOf Nat

public export
record Box where
  constructor MkBox
  widthOf : Nat
  height : Nat

export
sizeOf : Measure -> Nat
sizeOf (SizeOf n) = n

export
area : Box -> Nat
area b = b.widthOf * b.height

-- lint: allow of-name: a suppression the rule does not take
export
boxArea : Box -> Nat
boxArea b = halfOf (2 * area b)
  where
    halfOf : Nat -> Nat
    halfOf n = div n 2
