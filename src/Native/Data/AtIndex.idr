||| That a list has a value at a position (`AtIndex`), counted from its
||| front: what a variable of the term IR proves of its context, and what a
||| random-access list's lookups prove of the list they stand for. Proofs of
||| it are erased wherever they are used, so they cost nothing at run time.
|||
||| A position of a list made by `++` is one of either part: below the left
||| part's length it is the same position of the left part (`inLeft`,
||| `fromLeft`); from that length on it is the position less the length, of
||| the right part (`inRight`, `fromRight`).
module Native.Data.AtIndex

import Data.Nat

%default total

||| That the list has the value at the position, counted from its front.
public export
data AtIndex : Nat -> a -> List a -> Type where
  First : AtIndex Z x (x :: xs)
  Later : AtIndex n x xs -> AtIndex (S n) x (y :: xs)

||| The empty list has nothing at any position.
export
Uninhabited (AtIndex i x []) where
  uninhabited First impossible
  uninhabited (Later _) impossible

||| A position a list has a value at is below its length.
export
0 belowLength : AtIndex i x xs -> LT i (length xs)
belowLength First = LTESucc LTEZero
belowLength (Later p) = LTESucc (belowLength p)

||| A list has one value at a position.
export
0 unique : AtIndex i x xs -> AtIndex i y xs -> x = y
unique First First = Refl
unique (Later p) (Later q) = unique p q

||| What the left part has at a position, the whole has there.
export
0 inLeft : AtIndex i x l -> AtIndex i x (l ++ r)
inLeft First = First
inLeft (Later p) = Later (inLeft p)

||| What the right part has at a position less the left part's length, the
||| whole has at the position.
export
0 inRight : (l : List a) -> LTE (length l) i -> AtIndex (minus i (length l)) x r ->
            AtIndex i x (l ++ r)
inRight [] _ p = replace {p = \j => AtIndex j x r} (minusZeroRight i) p
inRight (_ :: l) (LTESucc le) p {i = S i} = Later (inRight l le p)

||| What the whole has at a position below the left part's length, the left
||| part has there.
export
0 fromLeft : (l : List a) -> LT i (length l) -> AtIndex i x (l ++ r) -> AtIndex i x l
fromLeft (_ :: _) _ First = First
fromLeft (_ :: l) (LTESucc lt) (Later p) = Later (fromLeft l lt p)

||| What the whole has at a position from the left part's length on, the
||| right part has at the position less the length.
export
0 fromRight : (l : List a) -> LTE (length l) i -> AtIndex i x (l ++ r) ->
              AtIndex (minus i (length l)) x r
fromRight [] _ p = replace {p = \j => AtIndex j x r} (sym (minusZeroRight i)) p
fromRight (_ :: l) (LTESucc le) (Later p) = fromRight l le p
