-- Types as values, printed: a function that matches on a type, a type
-- kept as an implicit argument and matched where it is used, and many
-- types made, held in a list across collections and counted by their
-- outermost constructor.
--
-- Where a program matches on a type, the type is not erased: it is a value
-- at run time, its type constructor and its arguments. So
--
--     describe : Type -> String
--     describe (List a) = "List of " ++ describe a
--
-- takes `List Nat` as the constructor `List` holding `Nat`, matches the
-- constructor, and binds `a` to the `Nat` it holds. `->` is a type
-- constructor too, of the argument's type and the result's, and so is
-- `Type`. A type matched by none of the alternatives takes the default
-- one. Idris's own parser does this, to decorate a name differently from
-- anything else (`decorationFromBounded {a = Name}`).
module Main

import Data.List
import Data.Maybe

-- a type, described by matching on it
describe : Type -> String
describe Nat = "Nat"
describe Bool = "Bool"
describe String = "String"
describe Int = "Int"
describe (List a) = "List of " ++ describe a
describe (Maybe a) = "Maybe " ++ describe a
describe (Pair a b) = "Pair of " ++ describe a ++ " and " ++ describe b
describe (a -> b) = "a function of " ++ describe a
describe Type = "Type"
describe _ = "something else"

-- a value labelled by its type, which the implicit `a` holds at run time
-- because the definition matches on it
label : {a : Type} -> a -> String
label {a = String} s = "the string " ++ s
label {a = Nat} n = "the number " ++ show n
label _ = "a value"

-- the outermost constructor's name, of a few
outer : Type -> String
outer (List _) = "List"
outer (Maybe _) = "Maybe"
outer _ = "other"

-- n types, alternating, each made afresh: List (Maybe Nat), Maybe Bool,
-- Nat; under a tiny allocation window the conses of the list and the
-- types they hold are moved by the collector while the list grows
made : Nat -> Int -> List Type -> List Type
made Z _ acc = acc
made (S k) i acc = made k (i + 1) (pick (mod i 3) :: acc)
  where
    pick : Int -> Type
    pick 0 = List (Maybe Nat)
    pick 1 = Maybe Bool
    pick _ = Nat

main : IO ()
main = do
  traverse_ (putStrLn . describe)
    [ Nat, Bool, String, Int, List Nat, List (List Bool), Maybe String
    , Pair Nat (List Int), (Int -> Bool), Type, Integer, Either Nat Bool ]
  putStrLn (label "hello")
  putStrLn (label (the Nat 42))
  putStrLn (label True)
  let ts = made 900 0 []
  putStrLn (show (length (filter ((== "List") . outer) ts)) ++ " lists")
  putStrLn (show (length (filter ((== "Maybe") . outer) ts)) ++ " maybes")
  putStrLn (describe (fromMaybe Type (head' ts)))
