-- The names a flat directive gives, which only the compilation of a program
-- reports, since a directive does not say which module wrote it: one that
-- names no function, and one that names two, the program's own `swap` and
-- the Prelude's. Qualified, the second is the program's, and is flat.

%cg native flat missing

swap : (Bits64, Bits64) -> (Bits64, Bits64)
swap (a, b) = (b, a)

%cg native flat swap

main : IO ()
main = printLn (swap (1, 2))
