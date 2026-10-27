-- A program that shows a double, and reads none, with one constant marked
-- static of its own, `squares`, as `NoDouble`'s. It prints half of word
-- 3 of `squares` as a double, 4.5: `printLn x` of a double is
-- `putStrLn (show x)`, and `show x` is the cast `cast {to = String} x`,
-- which the lowering makes a call of the string routine `showDouble`.
-- That routine finds the shortest digits with the runtime's table of
-- powers of ten, `powerOfTen`, a constant marked static, so the code
-- generator computes that table as it compiles the program, and lays out
-- its object before `squares`', whose name comes after it. The table that
-- only the reading of a decimal reads, `exactPowerOfTen`, is not computed.
module Main

import Native.Types.Bytes

%default covering

%cg native static Main.squares

-- Words a maker made, as if written
--
--   squares = <a BYTES object: its header, then the words 0, 1, 4, ..., 49>
squares : Bytes
squares = generate 8 (\i => cast (i * i))

main : IO ()
main = printLn (cast {to = Double} (uncheckedWord squares 3 0) / 2.0)
