-- Recursion that is not a tail call, in flat code, which runs on the
-- machine stack: a depth the stack holds, then one it does not, which ends
-- the program with a message.
module Main

import System

%cg native flat Main.depth
depth : Bits64 -> Bits64
depth 0 = 0
depth n = 3 + depth (n - 1)

%noinline
given : Bits64 -> Bits64
given x = x

main : IO ()
main = do
  if depth (given 10000) == 30000 then pure () else exitWith (ExitFailure 3)
  exitWith (if depth (given 100000000) == 300000000 then ExitSuccess else ExitFailure 4)
