-- A function marked twice, under two spellings of its name, is one flat
-- function: its error is reported once. An operator is marked as it is
-- written in a program, in parentheses.
module Twice

export infixl 8 +!

%cg native flat f Twice.f
f : String -> Bits64
f _ = 0

%cg native flat Twice.(+!)
(+!) : Bits64 -> Bits64 -> Bits64
a +! b = a + b

main : IO ()
main = printLn (f "x" +! 1)
