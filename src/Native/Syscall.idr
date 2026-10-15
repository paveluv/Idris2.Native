||| The raw system call (`prim__syscall6`): one instruction that hands the
||| kernel a number and six arguments and takes back its result, on the
||| operating systems that keep a stable system-call ABI.
|||
||| An inline extern of the contract (`Native.Intrinsics` says what they
||| are), apart from the others because only the modules that implement the
||| OS services may import it (the linter's `syscall`): the rest of the
||| runtime asks for services (`Native.Services`), which on other operating
||| systems are not system calls.
module Native.Syscall

import Native.Heap

%default total

||| A system call: its number and six arguments in, its result out, by the
||| architecture's and the operating system's convention.
export
%extern prim__syscall6 : (n, a1, a2, a3, a4, a5, a6 : Bits64) -> (1 m : Heap) -> Heap.Ret Heap Bits64
