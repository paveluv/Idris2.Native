-- A private primitive, and the function its own module writes with it.
module Mem

%foreign "C:labs,libc"
prim__abs : Int -> Int

%cg native flat Mem.magnitude
export
magnitude : Int -> Int
magnitude x = prim__abs x
