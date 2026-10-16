||| The raw system call: one instruction that hands the kernel a number and
||| six arguments and takes back its result, on the operating systems that
||| keep a stable system-call ABI. Only the modules that implement the OS
||| services import it; the rest of the runtime asks for services
||| (`Native.Runtime.OS`), which on other operating systems are not system
||| calls. The extern is declared here, privately; `externs` is the record
||| of it, checked against its port (`Native.Syscall`), which the code
||| generator reads.
module Native.Runtime.OS.Syscall

import Native.HeapObj.Shape as HeapObj
-- lint: allow import-unused: the record's fields unfold to its ports' types, which
-- Idris compares with the record's entries only where `Native.Port` is imported
import Native.Port
import Native.Runtime.Heap
import Native.Runtime.PortTy
import Native.Syscall

%default total

%extern prim__syscall6 : (n, a1, a2, a3, a4, a5, a6 : Bits64) -> (1 m : Heap) -> Heap.Ret Heap Bits64

||| The system call's extern, checked against its port.
export
externs : Syscall PortTy.ExternTy
externs = MkSyscall { syscall6 = prim__syscall6 }

||| A system call: its number and six arguments in, its result out, by the
||| architecture's and the operating system's convention.
export %inline
syscall : (n, a1, a2, a3, a4, a5, a6 : Bits64) -> Heap.Op Heap Bits64
syscall = prim__syscall6
