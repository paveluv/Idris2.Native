-- A private primitive, and the function its own module writes with it. A
-- primitive is a function the program does not define in Idris, here a
-- foreign C function, which a flat function calls with flat values. The flat
-- regime keeps its privacy by module: a private primitive is used only in
-- code its own module wrote, as `magnitude` here, or the Prelude's `putChar`,
-- which uses the Prelude's private `prim__putChar`.
module Mem

%foreign "C:labs,libc"
prim__abs : Int -> Int

%cg native flat Mem.magnitude
export
magnitude : Int -> Int
magnitude x = prim__abs x
