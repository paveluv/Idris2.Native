-- The names a flat directive gives, which only the compilation of a program
-- reports, since a directive does not say which module wrote it: one that
-- names no function, and one that names two, the program's own `swap` and
-- the Prelude's. Qualified, the second is the program's, and is flat.
--
-- A directive names functions as Idris prints names, qualified as far as it
-- takes to tell them apart: `Main.swap` here, since the Prelude's `swap`
-- exists too. It may come before or after the function. The test then
-- compiles this file with the second directive qualified and the first
-- deleted, and runs it.

%cg native flat missing

swap : (Bits64, Bits64) -> (Bits64, Bits64)
swap (a, b) = (b, a)

%cg native flat swap

main : IO ()
main = printLn (swap (1, 2))
