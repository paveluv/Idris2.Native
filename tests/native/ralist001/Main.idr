||| Random-access lists (`Native.Data.RAList`) checked against the lists
||| they stand for.
|||
||| An `RAList p xs` holds a value of `p x` for each element `x` of `xs`, as
||| `All p xs` does. Here `p` is `Singleton`, whose one value for `x` is
||| `Val x`, so that what a lookup finds can be compared with the element of
||| the list: the list `[10, 11, 12]` is held as
|||
|||     small : RAList Singleton [10, 11, 12]
|||     small = [Val 10, Val 11, Val 12]
|||
||| which is `Val 10 :: Val 11 :: Val 12 :: []`, each `::` putting a value in
||| front: `Val 12` and `Val 11` each a tree of one, then `Val 10` the root
||| over those two, so that `small` is one tree of three,
|||
|||     Node (Val 10) (Leaf (Val 11)) (Leaf (Val 12))
|||
||| its values in their order from the root, then left, then right.
||| `fetch 2 (Later (Later First)) small` is `Val 12`: the proof says that
||| position 2 of the list is 12, and `fetch` takes it, so it cannot miss;
||| position 2 is past the root and the left tree's one value, so it goes
||| right. `lookup 1 small` finds `Val 11` with the proof that 11 is at
||| position 1, and `lookup 3 small` finds nothing: the list has 3 elements.
|||
||| Lists of 0 to 300 elements are made four ways: a value put in front at
||| a time, the values of a first part put in front of a list of the rest,
||| at every place the list can be cut in two, from an `All`, and from the
||| list itself, `fromList [10, 11, 12]` being `small`. Each is looked up
||| at every position, by `fetch` and by `lookup`, and past its end, and its
||| size is compared with the list's length.
module Main

import Data.List.Quantifiers
import Data.Singleton
import Native.Data.AtIndex
import Native.Data.RAList

%default total

-- The three elements of the comments above.
small : RAList Singleton [10, 11, 12]
small = [Val 10, Val 11, Val 12]

-- A position of a list with its element and the erased proof that the
-- element is there: position 2 of `[10, 11, 12]` is 12, by
-- `Later (Later First)`.
record Position (xs : List Nat) where
  constructor MkPosition
  position : Nat
  element : Nat
  0 at : AtIndex position element xs

-- Every position of a list: `0` is its first element's, by `First`, and
-- each position of the rest is one more in the whole, by `Later`.
positions : (xs : List Nat) -> List (Position xs)
positions [] = []
positions (x :: xs) = MkPosition 0 x First :: map later (positions xs)
  where
    later : Position xs -> Position (x :: xs)
    later (MkPosition i y at) = MkPosition (S i) y (Later at)

-- A list cut in two, with the erased proof that the parts make it.
record Cut (xs : List Nat) where
  constructor MkCut
  front : List Nat
  back : List Nat
  0 joined : front ++ back = xs

-- Every place a list can be cut: `[] ++ xs`, then `[x0] ++ rest`, and so
-- on to `xs ++ []`.
cuts : (xs : List Nat) -> List (Cut xs)
cuts [] = [MkCut [] [] Refl]
cuts (x :: xs) = MkCut [] (x :: xs) Refl :: map later (cuts xs)
  where
    later : Cut xs -> Cut (x :: xs)
    later c = MkCut (x :: c.front) c.back (cong (x ::) c.joined)

-- The values for a list's elements, as an `All`: `[Val x0, Val x1, ...]`.
singletons : (xs : List Nat) -> All Singleton xs
singletons [] = []
singletons (x :: xs) = Val x :: singletons xs

-- A value put in front at a time: `Val x0 :: (Val x1 :: (... :: []))`.
byCons : (xs : List Nat) -> RAList Singleton xs
byCons [] = []
byCons (x :: xs) = Val x :: byCons xs

-- The front's values put in front of a list of the back's, the list made
-- the cut list by the proof that the parts make it.
byPrepend : Cut xs -> RAList Singleton xs
byPrepend c =
  replace {p = RAList Singleton} c.joined (prepend (singletons c.front) (byCons c.back))

-- Whether a random-access list holds the list's elements: at each
-- position `fetch` and `lookup` give the element there, `lookup` gives
-- nothing at the next three positions past the end, and the size is the
-- list's length.
holds : (xs : List Nat) -> List (Position xs) -> RAList Singleton xs -> Bool
holds xs ps r =
  let n = length xs in all fetched ps && all found ps && all beyond [n, S n, S (S n)] && size r == n
  where
    fetched : Position xs -> Bool
    fetched p = unVal (fetch p.position p.at r) == p.element

    found : Position xs -> Bool
    found p = case lookup p.position r of
      Just f => unVal f.value == p.element
      Nothing => False

    beyond : Nat -> Bool
    beyond i = case lookup i r of
      Just _ => False
      Nothing => True

-- The list of n elements the checks are made on, n * 1000 and on: no two
-- lengths share an element.
elements : Nat -> List Nat
elements n = go (n * 1000) n
  where
    go : Nat -> Nat -> List Nat
    go _ Z = []
    go x (S k) = x :: go (S x) k

-- How many of the lists made one way hold their elements, of how many.
report : String -> List Bool -> IO ()
report how checks =
  putStrLn (how ++ ": " ++ show (length (filter id checks)) ++ " of " ++ show (length checks)
            ++ " lists hold their elements")

main : IO ()
main = do
  putStrLn ("small: fetch 2 gives " ++ show (unVal (fetch 2 (Later (Later First)) small))
            ++ ", lookup 1 " ++ show (map (\f => unVal f.value) (lookup 1 small))
            ++ ", lookup 3 " ++ show (map (\f => unVal f.value) (lookup 3 small))
            ++ ", size " ++ show (size small))
  let lists = map elements [0 .. 300]
  report "by cons" (map (\xs => holds xs (positions xs) (byCons xs)) lists)
  -- each list's checks in front of the rest's, so that none is copied
  -- more than once
  report "by prepend"
    (foldr (\xs, rest => let ps = positions xs in map (holds xs ps . byPrepend) (cuts xs) ++ rest)
       [] lists)
  report "from All" (map (\xs => holds xs (positions xs) (fromAll (singletons xs))) lists)
  report "from List" (map (\xs => holds xs (positions xs) (fromList xs)) lists)
