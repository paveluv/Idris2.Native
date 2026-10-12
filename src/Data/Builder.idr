||| Results joined, from either side: what a pass makes by joining what its
||| recursive calls return (a tree walk's `go l <+> go r`, an instruction's
||| moves before the code of the rest), read once when the pass is done.
||| Joining costs nothing, whichever side is the longer, and reading out
||| costs the number of elements, once. The type has no other operation, so
||| no pass can copy what it has joined so far.
|||
||| Which structure an output takes follows its shape. A piece bounded by a
||| construct (an instruction's bytes, a call's arguments, a type's fields)
||| is a list, and so is a one-off join of two, where appending costs what
||| reading does. An accumulation that grows at its end, an element or a
||| piece at a time, is a `SnocList` (`:<`, `<><`, read out by `<>>`): each
||| step costs what it adds, less than a join here. Results joined from both
||| sides are a `Builder`: a list copies its left side at every join, and a
||| snoc-list its right, so one of them is quadratic whichever way the
||| results lean, and a builder is linear both ways.
|||
||| `concat` and `concatMap` on builders are linear, unlike on lists: they
||| fold with `<+>`, which costs nothing here.
module Data.Builder

%default total

export
data Builder : Type -> Type where
  Empty : Builder a
  Piece : List a -> Builder a
  Append : Builder a -> Builder a -> Builder a

export
Semigroup (Builder a) where
  Empty <+> b = b
  a <+> Empty = a
  a <+> b = Append a b

export
Monoid (Builder a) where
  neutral = Empty

||| A piece: a list bounded by a construct.
export
piece : List a -> Builder a
piece [] = Empty
piece xs = Piece xs

||| One element.
export
single : a -> Builder a
single x = Piece [x]

||| The elements, in order: each piece laid in front of what follows it,
||| so nothing is copied twice and nothing is reversed. The recursion into
||| the left is the tail call, so a builder that leans left is read in
||| constant stack, and one that leans right in stack as deep as it leans.
export
contents : Builder a -> List a
contents b = go b []
  where
    lay : List a -> List a -> List a
    lay [] rest = rest
    lay (x :: xs) rest = x :: lay xs rest

    go : Builder a -> List a -> List a
    go Empty rest = rest
    go (Piece xs) rest = lay xs rest
    go (Append l r) rest = go l (go r rest)

||| The lists `f` makes of the elements, joined in order, in linear time:
||| `concatMap` on lists folds from the left, copying what it has joined at
||| every step.
export
joinMap : (a -> List b) -> List a -> List b
joinMap f xs = contents (concatMap (piece . f) xs)
