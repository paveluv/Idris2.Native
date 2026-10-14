-- The probe's failures as the exit status: 0 when every check holds. The
-- program runs only natively: the runtime's inline externs are instructions of
-- the native code generator, and no other code generator has them.
module Main

import Data.So
import Probe
import System

exitCode : Int -> IO ()
exitCode n = case choose (n == 0) of
  Left _ => exitSuccess
  Right _ => exitWith (ExitFailure n)

main : IO ()
main = exitCode (cast (probe 0x1122334455667788))
