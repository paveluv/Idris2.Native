-- Ordinary code around the probe of `Probe.idr`. `probe` returns the count
-- the next collection makes, having seen the primitive not collect and
-- leave the window empty. Back in ordinary code, the first allocation,
-- whatever it is, takes the slow path and collects: exactly one, so the
-- count read afterwards is the one `probe` expected. The exit status is 0
-- when all of that holds.
module Main

import Data.List
import Data.So
import Flat.Uniform
import Probe
import Runtime.Space
import System

exitCode : Int -> IO ()
exitCode n = case choose (n == 0) of
  Left _ => exitSuccess
  Right _ => exitWith (ExitFailure n)

main : IO ()
main = do
  let pieces = replicate 64 (pack (replicate 4096 'a'))
  let expected = probe (MkUniform pieces)
  after <- collectionCount
  exitCode (if expected /= 0 && after == expected then 0 else 1)
