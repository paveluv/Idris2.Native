-- A program that declares an OS service's extern of its own, by the port
-- of `Exit`, which the runtime's module of the services declares already:
-- the code generator, which binds each service's one extern to the
-- platform's function for it, refuses the program, saying which.
module Main

import Native.HeapObj.Shape
import Native.Port
import Native.Runtime.Heap
import Native.Runtime.PortTy
import Native.Service

%extern service__again : PortTy.ExternTy (Service.port Service.Exit)

main : IO ()
main = putStrLn "not reached"
