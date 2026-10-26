-- A reference, made once: `cell` is a cell the program writes, which no
-- compilation may make for it. Its evaluation comes to the extern that
-- makes a reference (`prim__newIORef`), which only the running program
-- can run, and the mark is refused, with where.
module Extern

import Data.IORef

%cg native static Extern.cell

cell : IORef Int
cell = unsafePerformIO (newIORef 0)

main : IO ()
main = do
  modifyIORef cell (+ 1)
  printLn !(readIORef cell)
