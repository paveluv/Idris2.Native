-- Marks of constants whose values the prelude's functions between
-- strings and lists would compute of values Idris's types do not allow,
-- which `believe_me` makes: refused in one error that says why of each.
-- The code generator computes those functions as the runtime's string
-- module does of characters and strings, which hold Unicode scalar
-- values only; of another value the program's meaning is not certain.
--
-- * `surrogate` packs a list that holds the number 0xD800, which is no
--   character but a surrogate's code: the runtime would write the three
--   bytes UTF-8 would give it, which no well-formed string holds;
-- * `numbers` concatenates a list of numbers, which are no strings;
-- * `number` unpacks a number, which is no string;
-- * `found` packs `Just 'x'`, which is no list: the runtime would read it
--   as a cell, its constructor's id that of `(::)`, and a tail past its
--   one field;
-- * `consShaped` packs `Two 'x' []`, which is no list though it has two
--   fields, as the cell `'x' :: []` has, and its tail is `[]`: the
--   runtime tells a cell by its constructor's id alone, and `Two`'s is
--   not that of `(::)`, so it would take the value for the end of the
--   list and give "", where reading it as a cell would give "x";
-- * `consNumbered` packs `One`, which is no list though it has no fields,
--   as `[]` has: its constructor's id is that of `(::)`, so the runtime
--   would read it as a cell, its head and tail past the object.
module Forged

%cg native static Forged.surrogate Forged.numbers Forged.number Forged.found
%cg native static Forged.consShaped Forged.consNumbered

-- A type of three constructors, whose ids are 0, 1 and 2, as Idris
-- numbers a type's constructors in the order they are declared: `[]`'s
-- is 0 and `(::)`'s 1. A type of three is of no shape Idris makes a list
-- of, so its values stay its own constructors.
data Three = Zero | One | Two Char (List Char)

surrogate : String
surrogate = pack (believe_me (the (List Int) [0xD800]))

numbers : String
numbers = fastConcat (believe_me (the (List Int) [1, 2]))

number : List Char
number = unpack (believe_me (the Int 5))

found : String
found = pack (believe_me (the (Maybe Char) (Just 'x')))

consShaped : String
consShaped = pack (believe_me (Two 'x' []))

consNumbered : String
consNumbered = pack (believe_me One)

main : IO ()
main = do
  putStrLn surrogate
  putStrLn numbers
  printLn number
  putStrLn found
  putStrLn consShaped
  putStrLn consNumbered
