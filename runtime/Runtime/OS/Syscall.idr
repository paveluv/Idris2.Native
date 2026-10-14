||| The raw system call: one instruction that hands the kernel a number and
||| six arguments and takes back its result, on the operating systems that
||| keep a stable system-call ABI. Only the modules that implement the OS
||| services import it; the rest of the runtime asks for services
||| (`Runtime.OS`), which on other operating systems are not system calls.
module Runtime.OS.Syscall

import Runtime.Heap

%default total

||| A system call: its number and six arguments in, its result out, by the
||| architecture's and the operating system's convention.
%extern prim__syscall6 : (n, a1, a2, a3, a4, a5, a6 : Bits64) -> (1 m : Heap) -> Heap.Ret Heap Bits64

export %inline
syscall : (n, a1, a2, a3, a4, a5, a6 : Bits64) -> Heap.Op Heap Bits64
syscall = prim__syscall6
