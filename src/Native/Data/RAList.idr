||| Random-access lists (`RAList p xs`): a value of `p x` for each element
||| `x` of a list `xs`, as `Data.List.Quantifiers.All p xs` holds them, but
||| put in front in constant time (`::`) and looked up at a position `i` in
||| a number of steps of the order of the smaller of `i` and the logarithm
||| of the length (`fetch`, `lookup`), where `All` takes `i` steps. A lookup
||| proves what it finds: `fetch` takes the erased proof that `xs` has `x`
||| at the position, `lookup` gives it.
|||
||| The values are held as a list of complete binary trees, each with its
||| size: Okasaki's skew-binary random-access lists ("Purely Functional
||| Random-Access Lists", 1995). A tree holds a stretch of the elements in
||| preorder, its root's first, then its left subtree's, then its right
||| one's: in a tree whose subtrees are of size s, position 0 is the root's,
||| position j + 1 is the left subtree's position j when j is below s, and
||| the right subtree's position j - s otherwise. Each size is one less than
||| a power of two, the sizes grow along the list, and only the first two
||| trees may be of one size: putting a value in front makes it the root of
||| those two when they are, and a leaf of its own otherwise, so each step
||| changes the front of the list alone, and a list of n elements has at
||| most about log2 n + 1 trees.
|||
||| A lookup at position i passes the trees in front of the one that holds
||| it, then goes down that tree: each tree passed and each step down takes
||| at least one off the position, there are at most about log2 n trees to
||| pass, and as many steps down. Each step compares the position with a
||| size the list holds, a tree's or a subtree's, and takes it off: no step
||| halves a number, which Idris does on a `Nat` by repeated subtraction.
|||
||| At run time a random-access list is its trees, their values and their
||| sizes: the list `xs` and every proof are erased.
module Native.Data.RAList

import Native.Data.AtIndex

import Data.List
import Data.List.Quantifiers
import Data.Nat

%default total

------------------------------------------------------------------------------
-- Trees

-- The number of elements of a complete binary tree of the rank: one at
-- rank zero, a root and two trees of the rank below otherwise.
0 treeSize : Nat -> Nat
treeSize Z = 1
treeSize (S k) = S (treeSize k + treeSize k)

-- A complete binary tree of the rank holding the values for `ys`, in
-- preorder.
data Tree : (p : a -> Type) -> (rank : Nat) -> List a -> Type where
  Leaf : {0 x : a} -> p x -> Tree p Z [x]
  Node : {0 x : a} -> {0 l, r : List a} -> p x -> Tree p k l -> Tree p k r ->
         Tree p (S k) (x :: l ++ r)

0 appendLength : (l, r : List a) -> length (l ++ r) = length l + length r
appendLength [] _ = Refl
appendLength (_ :: l) r = cong S (appendLength l r)

-- The size of a tree of the rank, with those of the trees below it down to
-- a leaf's: what a step down a tree compares the position with is the
-- size of the subtree, held here, not its own size halved.
data Sizes : (rank : Nat) -> Type where
  One : Sizes Z
  Twice : (n : Nat) -> (0 _ : n = treeSize (S k)) -> Sizes k -> Sizes (S k)

-- The number of elements of a tree of the sizes.
count : Sizes k -> Nat
count One = 1
count (Twice n _ _) = n

0 countSize : (s : Sizes k) -> count s = treeSize k
countSize One = Refl
countSize (Twice _ size _) = size

-- What a tree holds, by its sizes.
0 countLength : {0 ys : List a} -> (s : Sizes k) -> Tree p k ys -> count s = length ys
countLength s t = trans (countSize s) (sym (treeLength t))
  where
    -- A tree holds as many elements as its rank says.
    0 treeLength : Tree p' k' ys' -> length ys' = treeSize k'
    treeLength (Leaf _) = Refl
    treeLength (Node {l} {r} _ left right) =
      cong S (trans (appendLength l r) (cong2 (+) (treeLength left) (treeLength right)))

-- The sizes of a root over two trees of the sizes.
twice : Sizes k -> Sizes (S k)
twice s = Twice (S (count s + count s)) (cong (\n => S (n + n)) (countSize s)) s

------------------------------------------------------------------------------
-- Comparisons, with the proofs of their outcomes

-- What `<` says of two numbers, as proofs.
0 below : (i, n : Nat) -> (i < n) = True -> LT i n
below Z Z Refl impossible
below Z (S _) _ = LTESucc LTEZero
below (S _) Z Refl impossible
below (S i) (S n) lt = LTESucc (below i n lt)

0 notBelow : (i, n : Nat) -> (i < n) = False -> LTE n i
notBelow _ Z _ = LTEZero
notBelow Z (S _) Refl impossible
notBelow (S i) (S n) ge = LTESucc (notBelow i n ge)

-- Whether a position is below a list's length, with the proof either way.
data Within : Nat -> List a -> Type where
  Inside : (0 _ : LT i (length ys)) -> Within i ys
  Beyond : (0 _ : LTE (length ys) i) -> Within i ys

-- Whether a position is within a list, by a number that is its length.
within : {0 ys : List a} -> (i, n : Nat) -> (0 _ : n = length ys) -> Within i ys
within i n eq with (i < n) proof lt
  _ | True = Inside (replace {p = LT i} eq (below i n lt))
  _ | False = Beyond (replace {p = \m => LTE m i} eq (notBelow i n lt))

-- What the right part of a list has at a position less a number that is
-- the left part's length, the whole has at the position.
0 behind : (l : List a) -> n = length l -> LTE (length l) i -> AtIndex (minus i n) x r ->
           AtIndex i x (l ++ r)
behind l Refl le at = AtIndex.inRight l le at

-- A position of a list beyond its left part, less that part's length, is
-- below the right part's length.
0 belowRight : (l : List a) -> n = length l -> LTE (length l) i -> LT i (length (l ++ r)) ->
               LT (minus i n) (length r)
belowRight l Refl le lt = go l le lt
  where
    go : (l' : List a) -> LTE (length l') j -> LT j (length (l' ++ r)) ->
         LT (minus j (length l')) (length r)
    go [] _ lt' = replace {p = \m => LT m (length r)} (sym (minusZeroRight j)) lt'
    go (_ :: l') (LTESucc le') (LTESucc lt') {j = S j} = go l' le' lt'

-- Two trees' ranks are one when their sizes are.
0 sameRank : (s : Sizes k) -> (s' : Sizes k') -> (count s == count s') = True -> k = k'
sameRank s s' eq = ranks k k' (trans (sym (countSize s)) (trans (equal _ _ eq) (countSize s')))
  where
    halves : (m, n : Nat) -> m + m = n + n -> m = n
    halves Z Z _ = Refl
    halves Z (S _) Refl impossible
    halves (S _) Z Refl impossible
    halves (S m) (S n) eq' =
      cong S (halves m n (cong pred (trans (plusSuccRightSucc m m)
        (trans (cong pred eq') (sym (plusSuccRightSucc n n))))))

    ranks : (j, j' : Nat) -> treeSize j = treeSize j' -> j = j'
    ranks Z Z _ = Refl
    ranks Z (S Z) Refl impossible
    ranks Z (S (S _)) Refl impossible
    ranks (S Z) Z Refl impossible
    ranks (S (S _)) Z Refl impossible
    ranks (S j) (S j') eq' = cong S (ranks j j' (halves _ _ (cong pred eq')))

    0 equal : (m, n : Nat) -> (m == n) = True -> m = n
    equal Z Z _ = Refl
    equal Z (S _) Refl impossible
    equal (S _) Z Refl impossible
    equal (S m) (S n) eq = cong S (equal m n eq)

------------------------------------------------------------------------------
-- Random-access lists

||| A random-access list: a value of `p x` for each element `x` of `xs`, in
||| complete binary trees, each with its sizes.
export
data RAList : (p : a -> Type) -> List a -> Type where
  Empty : RAList p []
  InFront : Sizes k -> Tree p k ys -> RAList p zs -> RAList p (ys ++ zs)

||| What a list has at a position: the element there, erased, the value for
||| it, and the erased proof that the element is there. At run time it is
||| the value alone.
public export
record Found (p : a -> Type) (i : Nat) (xs : List a) where
  constructor MkFound
  {0 element : a}
  value : p element
  0 at : AtIndex i element xs

-- The value at a position of a tree, below its size.
inTree : {0 ys : List a} -> Sizes k -> (j : Nat) -> (0 _ : LT j (length ys)) -> Tree p k ys ->
         Found p j ys
inTree _ Z _ (Leaf v) = MkFound v AtIndex.First
inTree _ (S _) lt (Leaf _) = void (succNotLTEzero (fromLteSucc lt))
inTree _ Z _ (Node v _ _) = MkFound v AtIndex.First
inTree (Twice _ _ s) (S j) lt (Node {l} _ left right) =
  case within j (count s) (countLength s left) of
    Inside inside =>
      let MkFound v at = inTree s j inside left in MkFound v (AtIndex.Later (AtIndex.inLeft at))
    Beyond beyond =>
      let MkFound v at = inTree s (minus j (count s))
                           (belowRight l (countLength s left) beyond (fromLteSucc lt)) right in
        MkFound v (AtIndex.Later (behind l (countLength s left) beyond at))

||| The list of no values.
export
Nil : RAList p []
Nil = Empty

||| The value put in front, in constant time: a leaf in front of the trees,
||| or the root of the first two when they are of one size.
export
(::) : {0 x : a} -> {0 xs : List a} -> p x -> RAList p xs -> RAList p (x :: xs)
v :: list@(InFront s t (InFront s' t' rest)) with (count s == count s') proof same
  _ | True = rooted v s t t' (sameRank s s' same) rest
    where
      rooted : p y -> Sizes k -> Tree p k l -> Tree p k' r -> (0 _ : k = k') -> RAList p zs ->
               RAList p (y :: l ++ (r ++ zs))
      rooted v' s'' left right Refl rest' =
        replace {p = \ys' => RAList p (y :: ys')} (sym (appendAssociative l r zs))
          (InFront (twice s'') (Node v' left right) rest')
  _ | False = InFront One (Leaf v) list
v :: list = InFront One (Leaf v) list

||| The values of an `All` put in front, in their order, in as many steps
||| as they are.
export
prepend : All p ys -> RAList p xs -> RAList p (ys ++ xs)
prepend [] list = list
prepend (v :: vs) list = v :: prepend vs list

||| The values, in as many steps as they are.
export
fromAll : All p xs -> RAList p xs
fromAll [] = []
fromAll (v :: vs) = v :: fromAll vs

||| The number of values, in as many steps as there are trees.
export
size : RAList p xs -> Nat
size Empty = 0
size (InFront s _ rest) = count s + size rest

||| The number of values is the length of the list.
export
0 sizeLength : (list : RAList p xs) -> size list = length xs
sizeLength Empty = Refl
sizeLength (InFront {ys} {zs} s t rest) =
  trans (cong2 (+) (countLength s t) (sizeLength rest)) (sym (appendLength ys zs))

||| The value for the element at a position, which the erased proof says the
||| list has: the trees in front of it passed, then down its tree, each step
||| taking at least one off the position.
export
fetch : (i : Nat) -> (0 _ : AtIndex i x xs) -> RAList p xs -> p x
fetch _ at Empty = void (uninhabited at)
fetch i at (InFront {ys} s t rest) = case within i (count s) (countLength s t) of
  Inside inside =>
    let MkFound v at' = inTree s i inside t in
        replace {p} (AtIndex.unique at' (AtIndex.fromLeft ys inside at)) v
  Beyond beyond => fetch (minus i (count s)) (past ys (countLength s t) beyond at) rest
  where
    -- What the whole has at a position from the left part's length on, the
    -- right part has at the position less a number that is the length.
    0 past : (l : List a) -> n = length l -> LTE (length l) i' -> AtIndex i' x' (l ++ r) ->
             AtIndex (minus i' n) x' r
    past l Refl le at = AtIndex.fromRight l le at

-- What the trees still to pass, those of `zs`, have at a position, as
-- `lookup` finds it, with how a position of `zs` is one of `xs`.
lookupFrom : {0 i : Nat} -> {0 xs : List a} -> (j : Nat) -> RAList p zs ->
             (0 _ : forall y . AtIndex j y zs -> AtIndex i y xs) -> Maybe (Found p i xs)
lookupFrom _ Empty _ = Nothing
lookupFrom j (InFront {ys} s t rest) into = case within j (count s) (countLength s t) of
  Inside inside =>
    let found = inTree s j inside t in
        Just (MkFound found.value (into (AtIndex.inLeft found.at)))
  Beyond beyond =>
    lookupFrom (minus j (count s)) rest (\at => into (behind ys (countLength s t) beyond at))

||| What the list has at a position, as `fetch` finds it, and `Nothing`
||| exactly when the position is not below the list's length
||| (`nothingPast`, `pastNothing`).
export
lookup : (i : Nat) -> RAList p xs -> Maybe (Found p i xs)
lookup i list = lookupFrom i list (\at => at)

-- A position past the left part, and past the right part from there on, is
-- past the whole.
0 pastBoth : (l, r : List a) -> LTE (length l) j -> LTE (length r) (minus j (length l)) ->
             LTE (length (l ++ r)) j
pastBoth l r le le' =
  replace {p = \m => LTE m j} (sym (appendLength l r))
    (replace {p = LTE (length l + length r)}
      (trans (plusCommutative (length l) (minus j (length l))) (plusMinusLte (length l) j le))
      (plusLteMonotoneLeft (length l) (length r) (minus j (length l)) le'))

-- Where the trees still to pass find nothing, the position is past them.
0 pastFrom : {0 xs, zs : List a} -> (j : Nat) -> (list : RAList p zs) ->
             (0 into : forall y . AtIndex j y zs -> AtIndex i y xs) ->
             lookupFrom j list into = Nothing -> LTE (length zs) j
pastFrom j Empty _ _ = LTEZero
pastFrom j (InFront {ys} {zs = rs} s t rest) _ none with (within j (count s) (countLength s t))
  _ | Inside _ = absurd none
  _ | Beyond beyond =
    pastBoth ys rs beyond
      (replace {p = \n => LTE (length rs) (minus j n)} (countLength s t)
        (pastFrom (minus j (count s)) rest _ none))

||| Where `lookup` finds nothing, the position is not below the length.
export
0 nothingPast : {0 xs : List a} -> (i : Nat) -> (list : RAList p xs) ->
                lookup i list = Nothing -> LTE (length xs) i
nothingPast i list none = pastFrom i list (\at => at) none

||| At a position not below the length, `lookup` finds nothing.
export
0 pastNothing : {0 xs : List a} -> (i : Nat) -> (list : RAList p xs) -> LTE (length xs) i ->
                lookup i list = Nothing
pastNothing i list past with (lookup i list)
  _ | Nothing = Refl
  _ | Just found = absurd (LTEImpliesNotGT past (AtIndex.belowLength found.at))
