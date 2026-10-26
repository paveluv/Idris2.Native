-- A constant marked static in a module that the program `Flat` does not
-- import: `Tables` imports it, and does not re-export it, so as `Flat` is
-- built Idris has loaded `Tables` but not this module, and `Squares.squares`
-- names no definition it has. `Flat`'s flat function `squareAt` reaches
-- the constant through `Tables.square`, so the check of flat functions as
-- `Flat` is built (`flat-check`) loads this module first, then finds what
-- the directive marks: the name resolved before the loading would name
-- nothing, and the constant's body would be translated as flat code, the
-- maker's with it, which flat code cannot hold.
module Squares

import Native.Types.Bytes

%default covering

%cg native static Squares.squares

-- Words a maker made, as if written
--
--   squares = <a BYTES object: its header, then the words 0, 1, 4, ..., 49>
export
squares : Bytes
squares = generate 8 (\i => cast (i * i))
