||| The direct system call: one instruction that hands the kernel a number and
||| six arguments and takes back its result, on the operating systems that
||| keep a stable system-call ABI. Only the modules that implement the OS
||| services import it; the rest of the runtime asks for services
||| (`Native.Runtime.OS`), which on other operating systems are not system
||| calls. The extern is an inline extern (`Native.Intrinsic`), declared here,
||| privately, by its port.
module Native.Runtime.OS.Syscall

import Native.Intrinsic
import Native.Runtime.Ordo
import Native.Runtime.PortTy

%default total

%extern intrinsic__syscall6 : PortTy.ExternTy (Intrinsic.port Intrinsic.Syscall6)

||| A system call: its number and six arguments in, its result out, by the
||| architecture's and the operating system's convention.
export %inline
syscall : (n, a1, a2, a3, a4, a5, a6 : Bits64) -> Ordo.Op Ordo Bits64
syscall = intrinsic__syscall6
