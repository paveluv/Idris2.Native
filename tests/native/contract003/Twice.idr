-- A program that declares an inline extern of its own, by the port of an
-- intrinsic the runtime declares already: `Load64` then has two externs,
-- and the code generator, which binds each intrinsic to the one extern of
-- its port, refuses the program, saying which.
module Main

import Native.HeapObj.Shape
import Native.Intrinsic
import Native.Port
import Native.Runtime.ByteAddr
import Native.Runtime.Ordo
import Native.Runtime.PortTy

%extern intrinsic__again : PortTy (Intrinsic.port Intrinsic.Load64)

main : IO ()
main = putStrLn "not reached"
