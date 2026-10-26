-- The C library's messages for its error numbers, as `strerror` gives
-- them: glibc's, for Linux's numbers, the runtime's own copy of them,
-- which the native code generator binds `strerror` to. A number of no
-- message, as 41 and 58 are, one below 0, or one above the last, 133, is
-- "Unknown error" and the number, as glibc says it. The expected output
-- holds the lines twice: native, and native under the encoding whose
-- pointers carry a tag.
--
-- Chez calls the C library's own `strerror`, whose messages are those of
-- the glibc it runs on, which change from one version to the next, so
-- this test does not compare with it.
module Main

import System.Errno

%default covering

main : IO ()
main = traverse_ (\n => putStrLn (show n ++ ": " ++ strerror n)) ([-1] ++ [0 .. 140] ++ [200])
