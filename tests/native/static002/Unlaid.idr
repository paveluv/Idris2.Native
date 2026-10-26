-- Marks of constants whose values the evaluation computes, but which the
-- code generator does not lay out as static data, refused in one error
-- that says why of each. `later` is a delayed value, which ordinary code
-- holds as a closure, as it holds a function: as if written
--
--   later = <a closure that computes 6 * 7 when forced>
--
-- `kind` is a type, which ordinary code holds as an object of its type
-- constructor. The others are constructors with fields, which the code
-- generator lays out, but whose fields hold such values, each said once,
-- however deep it is held: `halvers` a list of lambdas, and `adders` one
-- too, since Idris compiles the partial application `add 1` to a lambda
-- of the argument it leaves out, as if written
--
--   adders = [MkStep (\y => add 1 y)]
--
-- `kinds` a list of types, and `delays` a pair whose second field is a
-- list of delayed values.
module Unlaid

%cg native static Unlaid.later Unlaid.kind Unlaid.halvers Unlaid.adders Unlaid.kinds
%cg native static Unlaid.delays

later : Lazy Int
later = 6 * 7

kind : Type
kind = Int

-- A function to apply, as a record of one field, which Idris holds as the
-- function itself.
record Step where
  constructor MkStep
  apply : Int -> Int

add : Int -> Int -> Int
add x y = x + y

halvers : List Step
halvers = [MkStep (\x => x `div` 2)]

adders : List Step
adders = [MkStep (add 1)]

kinds : List Type
kinds = [Int, String]

delays : (Int, List (Lazy Int))
delays = (1, [2 + 3])

describe : Type -> String
describe t = case t of
  Int => "Int"
  _ => "another"

main : IO ()
main = do
  printLn (force later, describe kind, map (\s => s.apply 8) (halvers ++ adders))
  printLn (map describe kinds, map force (snd delays))
