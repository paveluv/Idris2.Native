||| The routines that end the program.
module Runtime.System

import public Runtime.OS

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

%cg native flat Runtime.System.exit
||| `idris_exit`: ends the process with the status.
export
exit : (status : Bits64) -> Op Heap ()
exit = osExit

%cg native flat Runtime.System.crash
||| `idris_crash`: writes the message, `length` bytes at `message`, to the
||| standard error, and ends the process with status 1.
export
crash : (message, length : Bits64) -> Op Heap ()
crash message length = do
  _ <- osWrite stderr message length
  exit 1
