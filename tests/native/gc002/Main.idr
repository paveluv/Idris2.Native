-- The heap limit a program sets on itself: with a limit of 256 KiB, a
-- copying collector may hold 128 KiB of data, and a list of 20000 cells,
-- 24 bytes each, is more. The runtime collects when the heap would cross
-- the limit, finds the data still too large, and ends the program with a
-- message and status 1. The first run, under no limit, keeps the same list
-- and exits with 0. A program would take its limit from its arguments;
-- `getArgs` is not lowered yet, so the test writes the limit into a copy.
module Main

import Data.So
import Native.Runtime.Space
import System

exitCode : Int -> IO ()
exitCode n = case choose (n == 0) of
  Left _ => exitSuccess
  Right _ => exitWith (ExitFailure n)

build : Int -> List Int -> List Int
build 0 acc = acc
build n acc = build (n - 1) (n :: acc)

main : IO ()
main = do
  pure ()   -- the limited program sets its limit here
  let keep = build 20000 []
  exitCode (if sum keep == 200010000 then 0 else 2)
