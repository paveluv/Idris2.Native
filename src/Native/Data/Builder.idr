||| Results joined, from either side: what a pass makes by joining what its
||| recursive calls return (a tree walk's `go l <+> go r`, an instruction's
||| moves before the code of the rest), used where it is when the pass is
||| done: folded (`Foldable`), taken an element at a time (`uncons`), or
||| written a piece at a time (`Data.WriteBuilder`), never first read out
||| into a list unless a list is what is wanted (`toList`). Joining costs
||| nothing, whichever side is the longer, and reading costs the number of
||| elements, once. The type has no other operation, so no pass can copy
||| what it has joined so far.
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
module Native.Data.Builder

%default total

||| A builder: nothing, a piece, or two builders joined. A join keeps the
||| number of nodes under it, itself included: no walk of a builder takes
||| more steps than that, which is how Idris knows each walk ends.
export
data Builder : Type -> Type where
  Empty : Builder a
  Piece : List a -> Builder a
  Append : (nodes : Nat) -> Builder a -> Builder a -> Builder a

||| The nodes of a builder: what bounds a walk of it.
nodes : Builder a -> Nat
nodes (Append n _ _) = n
nodes _ = 1

export
Semigroup (Builder a) where
  Empty <+> b = b
  a <+> Empty = a
  a <+> b = Append (S (nodes a + nodes b)) a b

export
Monoid (Builder a) where
  neutral = Empty

-- The walks the folds make, with the subtrees still to visit, each step
-- taking one node: a leaf off the list, or a join replaced by its two
-- parts. `foldr`'s walk takes a join's right part first, `foldl`'s and
-- `foldlM`'s its left. The fuel is the nodes left, which runs out as the
-- list does.

walkRight : (a -> b -> b) -> (fuel : Nat) -> List (Builder a) -> b -> b
walkRight f (S k) (Empty :: rest) acc = walkRight f k rest acc
walkRight f (S k) (Piece xs :: rest) acc = walkRight f k rest (foldr f acc xs)
walkRight f (S k) (Append _ l r :: rest) acc = walkRight f k (r :: l :: rest) acc
walkRight _ _ _ acc = acc

walkLeftM : Monad m => (b -> a -> m b) -> (fuel : Nat) -> b -> List (Builder a) -> m b
walkLeftM f (S k) acc (Empty :: rest) = walkLeftM f k acc rest
walkLeftM f (S k) acc (Piece xs :: rest) = foldlM f acc xs >>= \acc' => walkLeftM f k acc' rest
walkLeftM f (S k) acc (Append _ l r :: rest) = walkLeftM f k acc (l :: r :: rest)
walkLeftM _ _ acc _ = pure acc

||| A builder is read by folding it. Each fold walks the tree with the
||| subtrees it has still to visit in a list, never by recursion into one
||| side, so it runs in constant stack whichever way the builder leans:
||| a tree walk's results lean whichever way its recursion went. A piece,
||| bounded by a construct, is folded as a list.
|||
||| `foldr` visits the elements from the last, `foldl` from the first, and
||| `foldlM` from the first, each step's effect before the next. `foldMap`
||| folds from the right, so that even a builder of lists concatenates in
||| linear time: each list goes in front of what follows it. `toList` is the
||| elements in order, each laid once.
export
Foldable Builder where
  foldr f z b = walkRight f (nodes b) [b] z
  foldl f z b = walkLeft f (nodes b) z [b]
    where
      walkLeft : (b' -> a -> b') -> (fuel : Nat) -> b' -> List (Builder a) -> b'
      walkLeft f (S k) acc (Empty :: rest) = walkLeft f k acc rest
      walkLeft f (S k) acc (Piece xs :: rest) = walkLeft f k (foldl f acc xs) rest
      walkLeft f (S k) acc (Append _ l r :: rest) = walkLeft f k acc (l :: r :: rest)
      walkLeft _ _ acc _ = acc
  null Empty = True
  null _ = False
  foldlM f z b = walkLeftM f (nodes b) z [b]
  toList b = walkRight (::) (nodes b) [b] []
  foldMap f b = walkRight (\x, rest => f x <+> rest) (nodes b) [b] neutral

||| A piece: a list bounded by a construct.
export
piece : List a -> Builder a
piece [] = Empty
piece xs = Piece xs

||| One element.
export
single : a -> Builder a
single x = Piece [x]

||| The first element and the rest, for a reader that takes one element at
||| a time, in amortised constant time each: the builder's left spine is
||| turned to its right as the reader goes, each join once, so taking all
||| `n` elements costs `n` in all, in constant stack.
export
uncons : Builder a -> Maybe (a, Builder a)
uncons b = unconsWithin (nodes b) b
  where
    -- uncons's walk down the left spine, each step a node: past an empty part,
    -- or turning a join on the left to the right
    unconsWithin : (fuel : Nat) -> Builder a -> Maybe (a, Builder a)
    unconsWithin _ (Piece (x :: xs)) = Just (x, piece xs)
    unconsWithin (S k) (Append _ Empty r) = unconsWithin k r
    unconsWithin (S k) (Append _ (Piece []) r) = unconsWithin k r
    unconsWithin _ (Append _ (Piece (x :: xs)) r) = Just (x, piece xs <+> r)
    unconsWithin (S k) (Append _ (Append _ l m) r) = unconsWithin k (l <+> (m <+> r))
    unconsWithin _ _ = Nothing

||| The lists `f` makes of the elements, joined in order, in linear time:
||| `concatMap` on lists folds from the left, copying what it has joined at
||| every step.
export
joinMap : (a -> List b) -> List a -> List b
joinMap f xs = toList (concatMap (piece . f) xs)
