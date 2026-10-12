-- The string primitives with no value: the head and the tail of the empty
-- string, and a character at an index outside a string. The primitives are
-- partial, and so are `Data.String`'s `strTail` and `strIndex`, which are
-- them. Total code reaches them only behind a check, as `strUncons` checks
-- for the empty string first; a partial program can reach them anywhere.
--
-- Natively each ends the program with a message and status 1, before it
-- reads a byte outside the string. Under Chez, which Idris compiles without
-- bounds checks, only the tail ends it; the head and an index past the end
-- read whatever lies past the string.
--
-- The run script builds this program once for each, replacing the marked
-- line. `str` is not inlined, so the string is known only at run time and
-- nothing folds the call.
module Main

%noinline
str : String -> String
str x = x

||| Whether the result is a character no string here holds; either way the
||| program goes on to exit 0, if it gets there.
probe : Bool
probe = prim__strHead (str "") == 'z'   -- each program replaces this line

partial
main : IO ()
main = if probe then pure () else pure ()
