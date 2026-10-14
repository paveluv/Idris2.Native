||| What the runtime asks of the operating system: the OS services, the same
||| on every platform, which a module per platform implements as functions
||| of the services' names (`Runtime.OS.LinuxX86_64`). The generic runtime
||| calls a service through its `%extern` here; the native code generator
||| binds each, for the platform a program is compiled for, to that
||| platform's function. A service that can fail reports it, 1 for success
||| and 0 for failure, and the caller decides what a failure means.
module Runtime.OS

import Runtime.Heap

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

%extern prim__os_exit : (status : Bits64) -> (1 m : Heap) -> Heap.Ret Heap ()
%extern prim__os_write : (handle, address, bytes : Bits64) -> (1 m : Heap) -> Heap.Ret Heap Bits64
%extern prim__os_reserve : (bytes : Bits64) -> (1 m : Heap) -> Heap.Ret Heap Bits64
%extern prim__os_commit : (address, bytes : Bits64) -> (1 m : Heap) -> Heap.Ret Heap Bits64
%extern prim__os_release : (address, bytes : Bits64) -> (1 m : Heap) -> Heap.Ret Heap ()
%extern prim__os_stackLimit : (1 m : Heap) -> Heap.Ret Heap Bits64
%extern prim__os_pageBytes : (1 m : Heap) -> Heap.Ret Heap Bits64

||| End the process with the status.
export %inline
osExit : (status : Bits64) -> Heap.Op Heap ()
osExit = prim__os_exit

||| The standard handles: the output and the errors.
export
stdout, stderr : Bits64
stdout = 1
stderr = 2

||| Write `bytes` at the address to a standard handle; the bytes written.
export %inline
osWrite : (handle, address, bytes : Bits64) -> Heap.Op Heap Bits64
osWrite = prim__os_write

||| Reserve `bytes` of address space, readable by nothing and with no memory
||| committed to it; its address, 0 if the system has none.
export %inline
osReserve : (bytes : Bits64) -> Heap.Op Heap Bits64
osReserve = prim__os_reserve

||| Make `bytes` of reserved whole pages from the address readable,
||| writable and zero; 1 on success.
export %inline
osCommit : (address, bytes : Bits64) -> Heap.Op Heap Bits64
osCommit = prim__os_commit

||| Give `bytes` of committed whole pages from the address back to the
||| system, and reserve them again.
export %inline
osRelease : (address, bytes : Bits64) -> Heap.Op Heap ()
osRelease = prim__os_release

||| The most bytes the process's stack may grow to; 0 if the system does
||| not say.
export %inline
osStackLimit : Heap.Op Heap Bits64
osStackLimit = prim__os_stackLimit

||| The system's page: the bytes it commits and releases memory by.
export %inline
osPageBytes : Heap.Op Heap Bits64
osPageBytes = prim__os_pageBytes
