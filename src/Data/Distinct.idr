||| Whether no element of a list repeats (`distinct`): a switch's keys, a
||| program's names. It sorts, so it is quick on the thousands of names of a
||| program, and it is public, so that it reduces on a literal list where a
||| proof about one is searched for.
module Data.Distinct

%default total

public export
mergeSorted : Ord a => List a -> List a -> List a
mergeSorted [] ys = ys
mergeSorted xs [] = xs
mergeSorted (x :: xs) (y :: ys) = if x <= y then x :: mergeSorted xs (y :: ys) else y :: mergeSorted (x :: xs) ys

public export
halves : List a -> (List a, List a)
halves [] = ([], [])
halves [x] = ([x], [])
halves (x :: y :: zs) = let (as, bs) = halves zs in (x :: as, y :: bs)

||| The list, sorted.
public export
sorted : Ord a => List a -> List a
sorted [] = []
sorted [x] = [x]
-- lint: allow trust-escape: each half of a list of two or more is shorter than the list
sorted xs = let (as, bs) = halves xs in assert_total (mergeSorted (sorted as) (sorted bs))

||| Whether no element repeats: a switch's keys, a program's names. It sorts,
||| so it is quick on the thousands of names of a program.
public export
distinct : Ord a => List a -> Bool
distinct xs = apart (sorted xs)
  where
    apart : List a -> Bool
    apart (x :: y :: zs) = x /= y && apart (y :: zs)
    apart _ = True
