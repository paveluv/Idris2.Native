-- Recursion that is not a tail call, in flat code, which runs on the
-- machine stack: a depth the stack holds, then one it does not, which ends
-- the program with a message.
--
-- Ordinary code keeps its continuations on the heap, so its recursion is
-- bounded by memory alone. A flat function is a machine function: a call
-- that is not a tail call, such as `depth (n - 1)` before the `3 +`, pushes
-- a frame on the machine stack, as C would. Every flat function checks the
-- stack pointer against the limit the runtime set at start-up, so a
-- recursion too deep ends with `idris: stack overflow` and status 1, never
-- with a fault.
module Main

import System

%cg native flat Main.depth
depth : Bits64 -> Bits64
depth 0 = 0
depth n = 3 + depth (n - 1)

-- Not inlined, so the depths are known only at run time and nothing folds
-- the recursion away.
%noinline
given : Bits64 -> Bits64
given x = x

main : IO ()
main = do
  if depth (given 10000) == 30000 then pure () else exitWith (ExitFailure 3)
  exitWith (if depth (given 100000000) == 300000000 then ExitSuccess else ExitFailure 4)
