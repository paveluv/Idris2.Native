||| A builder used where it is (`Data.Builder`): folded, taken an element at
||| a time, and written to a file a piece at a time (`Data.WriteBuilder`).
|||
||| A builder is a tree of pieces: `single 1 <+> single 2` joins two leaves.
||| A pass that joins as it returns makes a tree that leans whichever way
||| its recursion went, so each reading here is tried on both: one leaning
||| left, `((1 <+> 2) <+> 3) <+> ...`, as a fold from the left joins, and
||| one leaning right, `1 <+> (2 <+> (3 <+> ...))`, as a fold from the right
||| does.
module Main

import Data.String
import Native.Data.Builder
import Native.Data.WriteBuilder
import System.File.ReadWrite

%default covering

-- the numbers 1 to n, joined one at a time onto the end
leaningLeft : Nat -> Builder Nat
leaningLeft n = foldl (\b, i => b <+> single i) neutral [1 .. n]

-- the same numbers, each joined in front of the rest
leaningRight : Nat -> Builder Nat
leaningRight n = foldr (\i, b => single i <+> b) neutral [1 .. n]

-- every element by `uncons`, one at a time, as a reader that cannot take
-- them all at once would: `Just (x, rest)` until `Nothing`
oneByOne : Builder Nat -> List Nat
oneByOne b = go b [<]
  where
    go : Builder Nat -> SnocList Nat -> List Nat
    go b acc = case uncons b of
      Nothing => acc <>> []
      Just (x, rest) => go rest (acc :< x)

-- what each reading of a builder of 1 to n says: its first and last
-- elements, its length, its sum folded from either side, and whether
-- taking it one element at a time gives the same list
readings : String -> Builder Nat -> IO ()
readings name b = do
  let xs = toList b
  putStrLn (name ++ ": first " ++ show (head' xs) ++ ", last " ++ show (last' xs)
            ++ ", length " ++ show (length xs)
            ++ ", sum from the left " ++ show (foldl (+) 0 b)
            ++ ", from the right " ++ show (foldr (+) 0 b)
            ++ ", one by one alike " ++ show (oneByOne b == xs))

main : IO ()
main = do
  -- 200000 joins either way: each fold walks the tree with the subtrees
  -- it has still to visit, not by recursion into one side
  readings "leaning left" (leaningLeft 200000)
  readings "leaning right" (leaningRight 200000)
  -- nothing joined is empty, and an empty piece adds nothing
  putStrLn ("empty: " ++ show (null (the (Builder Nat) neutral)) ++ ", "
            ++ show (null (piece (the (List Nat) []) <+> neutral)) ++ ", "
            ++ show (null (single (the Nat 1))))
  -- `foldMap` on a builder of lists puts each list in front of the rest:
  -- [1, 2] then [3] then [4, 5]
  putStrLn
    ("foldMap: "
     ++ show (foldMap id (single [1, 2] <+> single [3] <+> single (the (List Nat) [4, 5]))))
  -- a text in pieces written a piece at a time, then read back whole
  Right () <- writeBuilder "pieces.txt"
    (concatMap (\i => single ("line " ++ show i ++ "\n")) [the Nat 1 .. 3])
    | Left err => putStrLn ("cannot write: " ++ show err)
  Right text <- readFile "pieces.txt"
    | Left err => putStrLn ("cannot read: " ++ show err)
  putStr text
