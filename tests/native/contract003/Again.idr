-- A program that brings a module of the runtime's core of its own,
-- `Native.Runtime.SecondExit` (beside this file, under Native/Runtime/),
-- which declares an OS service's extern by the port of `Exit`, which the
-- runtime's module of the services declares already: the code generator,
-- which binds each service's one extern to the platform's function for
-- it, refuses the program, saying which.
module Main

import Native.Runtime.SecondExit

main : IO ()
main = putStrLn "not reached"
