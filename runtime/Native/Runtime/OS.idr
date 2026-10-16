||| What the runtime asks of the operating system: the OS services, the same
||| on every platform (`Native.Service` says what they are), each a call of
||| an `%extern` declared here, privately, by its service's port, and wrapped
||| for the rest of the runtime. A module per platform implements every
||| service by a function declared by the same port
||| (`Native.Runtime.OS.LinuxX86_64`), and the native code generator binds
||| each extern, for the platform a program is compiled for, to that
||| platform's function. A service that can fail reports it, 1 for success
||| and 0 for failure, and the caller decides what a failure means.
module Native.Runtime.OS

-- lint: allow public-import: an extern's type, written by its port, reduces only
-- where the port and its reading are visible, so they are wherever this
-- module is, whose wrappers the flat translation unfolds into its importers
import public Native.Port
import public Native.Runtime.PortTy
import public Native.Service

import Native.Runtime.Heap
import Native.Runtime.Raw

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

%extern service__exit : PortTy.ExternTy (Service.port Service.Exit)
%extern service__write : PortTy.ExternTy (Service.port Service.Write)
%extern service__reserve : PortTy.ExternTy (Service.port Service.Reserve)
%extern service__commit : PortTy.ExternTy (Service.port Service.Commit)
%extern service__release : PortTy.ExternTy (Service.port Service.Release)
%extern service__stackLimit : PortTy.ExternTy (Service.port Service.StackLimit)
%extern service__pageBytes : PortTy.ExternTy (Service.port Service.PageBytes)


||| End the process with the status.
export %inline
osExit : (status : Bits64) -> Heap.Op Heap ()
osExit = service__exit

||| The standard handles: the output and the errors.
export
stdout, stderr : Bits64
stdout = 1
stderr = 2

||| Write `bytes` at the address to a standard handle; the bytes written.
export %inline
osWrite : (handle : Bits64) -> (address : Raw) -> (bytes : Bits64) -> Heap.Op Heap Bits64
osWrite = service__write

||| Reserve `bytes` of address space, readable by nothing and with no memory
||| committed to it; its address, the null one if the system has none.
export %inline
osReserve : (bytes : Bits64) -> Heap.Op Heap Raw
osReserve = service__reserve

||| Make `bytes` of reserved whole pages from the address readable,
||| writable and zero; 1 on success.
export %inline
osCommit : (address : Raw) -> (bytes : Bits64) -> Heap.Op Heap Bits64
osCommit = service__commit

||| Give `bytes` of committed whole pages from the address back to the
||| system, and reserve them again.
export %inline
osRelease : (address : Raw) -> (bytes : Bits64) -> Heap.Op Heap ()
osRelease = service__release

||| The most bytes the process's stack may grow to; 0 if the system does
||| not say.
export %inline
osStackLimit : Heap.Op Heap Bits64
osStackLimit = service__stackLimit

||| The system's page: the bytes it commits and releases memory by.
export %inline
osPageBytes : Heap.Op Heap Bits64
osPageBytes = service__pageBytes

||| Write all `bytes` at the address to a standard handle, in as many writes
||| as it takes; a write that fails ends it, as nothing more would go.
export covering
osWriteAll : (handle : Bits64) -> (address : Raw) -> (bytes : Bits64) -> Heap.Op Heap ()
osWriteAll h a n =
  if n == 0 then Heap.pure () else do
    w <- osWrite h a n
    if w == 0 then Heap.pure () else osWriteAll h (Raw.offset a w) (n - w)
