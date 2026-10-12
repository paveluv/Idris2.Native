||| What a pass accumulates: an output being produced, read once when the
||| pass is done. Appending two costs nothing, whichever is the longer, and
||| reading out costs the number of elements, once. The type has no other
||| operation, so no loop over a `Builder` can copy what it has produced so
||| far, which a loop over a list does at every `++`, and none can reverse
||| it, which an accumulation in a list costs at the end.
|||
||| The rule it serves: an accumulation of unbounded length is a `Builder`;
||| a list is for a piece bounded by a construct (an instruction's bytes, a
||| call's arguments, a type's fields), where appending and reversing cost
||| what reading does. A value a pass has finished is read once, by
||| `contents`, into the list its consumer traverses.
|||
||| `concat` and `concatMap` on builders are linear, unlike on lists: they
||| fold with `<+>`, which costs nothing here.
module Data.Builder

%default total

export
data Builder : Type -> Type where
  Empty : Builder a
  Piece : (n : Nat) -> List a -> Builder a
  Append : (n : Nat) -> Builder a -> Builder a -> Builder a

||| The number of elements.
export
size : Builder a -> Nat
size Empty = 0
size (Piece n _) = n
size (Append n _ _) = n

export
Semigroup (Builder a) where
  Empty <+> b = b
  a <+> Empty = a
  a <+> b = Append (size a + size b) a b

export
Monoid (Builder a) where
  neutral = Empty

||| A piece: a list bounded by a construct.
export
piece : List a -> Builder a
piece [] = Empty
piece xs = Piece (length xs) xs

||| One element.
export
single : a -> Builder a
single x = Piece 1 [x]

||| The elements, in order: each piece laid in front of what follows it,
||| so nothing is copied twice and nothing is reversed. The recursion into
||| the left is the tail call, so an accumulation that grows on the right,
||| the usual one, is read in constant stack.
export
contents : Builder a -> List a
contents b = go b []
  where
    lay : List a -> List a -> List a
    lay [] rest = rest
    lay (x :: xs) rest = x :: lay xs rest

    go : Builder a -> List a -> List a
    go Empty rest = rest
    go (Piece _ xs) rest = lay xs rest
    go (Append _ l r) rest = go l (go r rest)
