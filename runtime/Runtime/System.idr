||| The system calls, and the routines that end the program.
module Runtime.System

import public Runtime.Heap

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| A system call: its number and six arguments in, its result out. The
||| numbers are Linux x86-64's.
%extern prim__syscall6 : (n, a1, a2, a3, a4, a5, a6 : Bits64) -> (1 m : Heap) -> Ret Heap Bits64

export %inline
syscall : (n, a1, a2, a3, a4, a5, a6 : Bits64) -> Op Heap Bits64
syscall = prim__syscall6

%cg native flat Runtime.System.exit
||| `idris_exit`: ends the process with the status.
export
exit : (status : Bits64) -> Op Heap ()
exit status = do
  -- exit_group(status)
  _ <- syscall 231 status 0 0 0 0 0
  pure ()

%cg native flat Runtime.System.crash
||| `idris_crash`: writes the message, `length` bytes at `message`, to the
||| standard error, and ends the process with status 1.
export
crash : (message, length : Bits64) -> Op Heap ()
crash message length = do
  -- write(2, message, length)
  _ <- syscall 1 2 message length 0 0 0
  exit 1
