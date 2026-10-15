||| The raw system call: one instruction that hands the kernel a number and
||| six arguments and takes back its result, on the operating systems that
||| keep a stable system-call ABI. Only the modules that implement the OS
||| services import it; the rest of the runtime asks for services
||| (`Native.Runtime.OS`), which on other operating systems are not system
||| calls.
module Native.Runtime.OS.Syscall

-- lint: allow public-import: the flat translation reaches through this module
-- (checking an importer's flat functions, it reaches the inline wrappers'
-- bodies, which use the contract's externs, so it is loaded wherever this
-- module is)
import public Native.Syscall

import Native.Heap

%default total

||| A system call: its number and six arguments in, its result out, by the
||| architecture's and the operating system's convention.
export %inline
syscall : (n, a1, a2, a3, a4, a5, a6 : Bits64) -> Heap.Op Heap Bits64
syscall = Syscall.prim__syscall6
