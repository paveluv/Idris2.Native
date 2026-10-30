||| A list's elements, each with its position (`numbered`), counted from 0
||| at its front.
module Native.Data.Numbered

%default total

||| Each element with its position, in one walk, with no list of the
||| positions made first.
export
numbered : List a -> List (Nat, a)
numbered = go 0
  where
    go : Nat -> List a -> List (Nat, a)
    go _ [] = []
    go i (x :: xs) = (i, x) :: go (S i) xs
