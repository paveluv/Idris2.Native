-- A program that brings a module of the runtime's support tier of its own,
-- `Native.Support.Leave` (beside this file, under Native/Support/), which
-- declares an OS service's extern by the port of `Exit` outside the
-- modules where the runtime declares its externs: the module's build
-- refuses it, saying where, and the program is not compiled.
module Main

import Native.Support.Leave

main : IO ()
main = putStrLn "not reached"
