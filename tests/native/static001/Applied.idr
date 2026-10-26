-- A constant marked static applied to an argument. `inc` takes one, so it
-- is no constant (`Function` shows the mark refused when the program is
-- compiled), and a flat function that applies it, as if written
--
--   useInc x = <inc's value> x
--
-- reads no value it could apply: a constant marked static has one value,
-- which no argument chooses. The flat function is refused as the module
-- is built, at the application, before the program is compiled.
module Applied

%cg native static Applied.inc
%cg native flat Applied.useInc

inc : Int -> Int
inc x = x + 1

useInc : Int -> Int
useInc x = inc x

main : IO ()
main = printLn (useInc 41)
