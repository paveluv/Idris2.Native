-- A program that shows no double, nor reads one, with one constant marked
-- static of its own, `squares`, words a maker made, as static002's are.
-- It prints word 3 of `squares`, 9, a `Bits64`: `printLn w` is
-- `putStrLn (show w)`, and `show w` is the cast `cast {to = String} w`,
-- which the lowering makes a call of the string routine `showUnsigned`.
-- No string routine its code may call reads a table of the runtime, so
-- the code generator computes none of them as it compiles the program:
-- `squares` is the only constant it computes, and its object the first
-- it lays out.
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
main = printLn (uncheckedWord squares 3 0)
