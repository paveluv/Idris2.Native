-- A module nested in `Mem` sees its private names, but the private
-- primitive is used where its own module did not write it.
module Mem.Leak

import Mem

%cg native flat Mem.Leak.leak
leak : Int -> Int
leak x = prim__abs x

main : IO ()
main = pure ()
