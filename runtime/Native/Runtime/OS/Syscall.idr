||| The raw system call: one instruction that hands the kernel a number and
||| six arguments and takes back its result, on the operating systems that
||| keep a stable system-call ABI. Only the modules that implement the OS
||| services import it; the rest of the runtime asks for services
||| (`Native.Runtime.OS`), which on other operating systems are not system
||| calls. The extern is an inline extern (`Native.Intrinsic`), declared
||| here, privately, by its port.
module Native.Runtime.OS.Syscall

-- lint: allow public-import: an extern's type, written by its port, reduces only
-- where the port and its reading are visible, so they are wherever this
-- module is, whose wrapper the flat translation unfolds into its importers
import public Native.Intrinsic
import public Native.Port
import public Native.Runtime.PortTy

import Native.Runtime.Heap

%default total

%extern intrinsic__syscall6 : PortTy.ExternTy (Intrinsic.port Intrinsic.Syscall6)

||| A system call: its number and six arguments in, its result out, by the
||| architecture's and the operating system's convention.
export %inline
syscall : (n, a1, a2, a3, a4, a5, a6 : Bits64) -> Heap.Op Heap Bits64
syscall = intrinsic__syscall6
