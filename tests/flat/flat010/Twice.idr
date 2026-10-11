-- A function marked twice, under two spellings of its name, is one flat
-- function: its error is reported once. An operator is marked as it is
-- written in a program, in parentheses.
--
-- One directive may name several functions, separated by spaces. The test
-- then deletes the first directive and the call of `f`, renames the module
-- `Operator`, and dumps the operator's flat form.
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
