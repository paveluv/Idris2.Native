||| The raw system call (`Syscall`): one instruction that hands the kernel
||| a number and six arguments and takes back its result, on the operating
||| systems that keep a stable system-call ABI. An inline extern, as those
||| of `Native.Intrinsics` are, apart from them because only the modules
||| that implement the OS services may make one (the linter's `syscall`):
||| the rest of the runtime asks for services (`Native.Services`), which on
||| other operating systems are not system calls. The runtime's
||| `Native.Runtime.OS.Syscall` declares the extern and gives the record.
|||
||| Part of the contract between compiled code and the runtime, with the
||| heap-object model (`HeapObj.Shape` says what it is).
module Native.Syscall

import Native.Port

%default total

||| The raw system call, a field of its port.
public export
record Syscall (f : Port -> Type) where
  constructor MkSyscall
  ||| A system call: its number and six arguments; its result.
  syscall6 : f
             (MkPort [Port.Word, Port.Word, Port.Word, Port.Word, Port.Word, Port.Word, Port.Word]
              (Just Port.Word))

||| The system call's entries of two records made one.
public export
zipSyscall : ({p : Port} -> f p -> g p -> h p) -> Syscall f -> Syscall g -> Syscall h
zipSyscall z a b = MkSyscall (z a.syscall6 b.syscall6)

||| The system call's entry, with its port.
public export
syscallList : Syscall f -> List (p : Port ** f p)
syscallList r = [(_ ** r.syscall6)]
