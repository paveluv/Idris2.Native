-- A buffer, made once: `buffer` is written by the program, and made by a
-- foreign function (`prim__newBuffer`), which only the running program
-- can run, so the mark is refused, with where.
module Foreign

import Data.Buffer

%cg native static Foreign.buffer

buffer : Buffer
buffer = unsafePerformIO $ do
  Just b <- newBuffer 8
    | Nothing => assert_total (idris_crash "no buffer")
  pure b

main : IO ()
main = do
  setBits64 buffer 0 7
  printLn !(getBits64 buffer 0)
