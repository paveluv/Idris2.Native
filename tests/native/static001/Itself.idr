-- A constant that needs its own value: computing `ones` reads `ones`.
-- Reading a constant takes no step of the evaluation, so no bound on its
-- steps would end it; the evaluation finds `ones` in its own value while
-- it computes it, and the mark is refused.
module Itself

import Data.List

%default covering

%cg native static Itself.ones

ones : List Integer
ones = 1 :: ones

main : IO ()
main = printLn (Data.List.take 3 ones)
