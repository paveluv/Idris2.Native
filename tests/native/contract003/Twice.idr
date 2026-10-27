-- A program that brings a module of the runtime's core of its own,
-- `Native.Runtime.SecondLoad` (beside this file, under Native/Runtime/),
-- which declares an inline extern by the port of an intrinsic the runtime
-- declares already: `Load64` then has two externs among the core's
-- modules, where the code generator looks for the intrinsics, and the code
-- generator, which binds each intrinsic to the one extern of its port,
-- refuses the program, saying which. Importing the module is enough: what
-- the program imports is loaded with it, used or not.
module Main

import Native.Runtime.SecondLoad

main : IO ()
main = putStrLn "not reached"
