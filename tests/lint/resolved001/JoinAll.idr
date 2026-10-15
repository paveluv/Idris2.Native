||| Accumulations, which `list-accumulation` reports, a warning, per
||| definition: a list grown at its end with `++`, and lists joined by a
||| left fold. Those written with the structure their shape asks for, a
||| snoc-list or a builder, count towards the score's `accumulation`.
module JoinAll

import Native.Data.Builder

%default total

||| Each element appended at the end of the list built so far: `acc ++ [x]`
||| copies `acc` at every step, so `n` elements cost about `n * n / 2`
||| copies. Reported.
export
joinAll : List Nat -> List Nat
joinAll = go []
  where
    go : List Nat -> List Nat -> List Nat
    go acc [] = acc
    go acc (x :: xs) = go (acc ++ [x]) xs

||| The same as a left fold's step, `\acc, x => acc ++ [x]`. Reported.
export
foldAll : List Nat -> List Nat
foldAll = foldl (\acc, x => acc ++ [x]) []

||| The same at a snoc-list's end, where adding costs what is added:
||| `acc :< x`, read out once by `<>>`. Counted as structured.
export
snocAll : List Nat -> List Nat
snocAll = go [<]
  where
    go : SnocList Nat -> List Nat -> List Nat
    go acc [] = acc <>> []
    go acc (x :: xs) = go (acc :< x) xs

||| A piece put in front of what is built so far, `x ++ acc`: only the
||| piece is copied, which is what a list does well. Not reported.
export
prependAll : List (List Nat) -> List Nat
prependAll = go []
  where
    go : List Nat -> List (List Nat) -> List Nat
    go acc [] = acc
    go acc (x :: xs) = go (x ++ acc) xs

||| `concat` on lists folds from the left, copying what it has joined at
||| every step. Reported.
export
flatten : List (List Nat) -> List Nat
flatten = concat

||| One join of two lists copies the first once, as the result must. Not
||| reported.
export
joinTwo : List Nat -> List Nat -> List Nat
joinTwo xs ys = xs ++ ys

||| Two builders joined, in constant time: counted as structured.
export
joinBuilt : Builder Nat -> Builder Nat -> Builder Nat
joinBuilt a b = a <+> b
