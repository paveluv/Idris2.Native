-- Marks of constants whose values the evaluation computes, but which the
-- code generator does not lay out as static data, refused in one error
-- that says why of each. `pair` is a constructor with fields, an object
-- whose fields the image would hold. `later` is a delayed value, which
-- ordinary code holds as a closure, as it holds a function: as if written
--
--   later = <a closure that computes 6 * 7 when forced>
--
-- `kind` is a type, which ordinary code holds as an object of its type
-- constructor.
module Unlaid

%cg native static Unlaid.pair Unlaid.later Unlaid.kind

pair : (Int, Int)
pair = (1, 2)

later : Lazy Int
later = 6 * 7

kind : Type
kind = Int

describe : Type -> String
describe t = case t of
  Int => "Int"
  _ => "another"

main : IO ()
main = printLn (fst pair, force later, describe kind)
