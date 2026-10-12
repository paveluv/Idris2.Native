-- The surface of `prelude` and `base` that reaches a code generator through
-- `%foreign` and `%extern`, and how the native one implements each piece:
-- `runtime` when the runtime has a function for it, `lowered` when the
-- lowering does it inline, `missing` when it is not done yet and a program
-- that reaches it ends with `idris: unsupported`. This is the checklist the
-- items that build the rest tick off: the golden changes as they do.
--
-- The program does nothing: it imports every module of `base` that declares
-- foreign functions, so that they are all in the context the listing reads.
module Main

import Data.Buffer
import Data.IORef
import Data.IOArray
import System
import System.Clock
import System.Concurrency
import System.Directory
import System.Errno
import System.FFI
import System.File
import System.Info
import System.Signal
import System.Term

main : IO ()
main = pure ()
