||| The routines that end the program.
module Native.Runtime.System

import Native.Runtime.Memory
import Native.Runtime.Ordo
import Native.Runtime.OS
import Native.Runtime.PortTy

import Native.HeapObj.Shape
import Native.Routine

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

%cg native flat Runtime.System.exit
||| `idris_exit`: ends the process with the status.
export
exit : (status : Bits64) -> Ordo.Op Ordo ()
exit = OS.osExit

%cg native flat Runtime.System.crash
||| `idris_crash`: writes the message, `length` bytes at `message`, to the
||| standard error, and ends the process with status 1.
export
crash : PortTy Memory.Addr (Routine.port Routine.Crash)
crash message length = do
  _ <- OS.osWrite OS.stderr message length
  exit 1
