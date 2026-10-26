-- Marked flat and static at once: a function is compiled in the flat
-- regime, or a constant's value is computed as the program is compiled,
-- not both.
module Both

%cg native flat Both.both
%cg native static Both.both

both : Bits64
both = 2 + 3

main : IO ()
main = printLn both
