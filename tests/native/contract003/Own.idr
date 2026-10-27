-- A program that declares, in its own module, externs by the ports of an
-- intrinsic and of an OS service, as the runtime's core declares its
-- own:
--
--     %extern intrinsic__own : PortTy (Intrinsic.port Intrinsic.Load64)
--     %extern service__own : PortTy (Service.port Service.Exit)
--
-- The code generator looks for the contract's externs only among the
-- runtime's, in the modules where the runtime declares them, so in a
-- program's own module these are ordinary externs, which it does not look
-- at: `Load64` and `Exit` still have one extern each, the runtime's, and
-- the program compiles, and runs. A program cannot pass for the runtime
-- this way either: the lowering knows an extern as an intrinsic, or a
-- service, only as one the code generator found.
module Main

import Native.HeapObj.Shape
import Native.Intrinsic
import Native.Port
import Native.Runtime.ByteAddr
import Native.Runtime.Ordo
import Native.Runtime.PortTy
import Native.Service

%extern intrinsic__own : PortTy (Intrinsic.port Intrinsic.Load64)
%extern service__own : PortTy (Service.port Service.Exit)

main : IO ()
main = putStrLn "the program's own externs are not the contract's"
