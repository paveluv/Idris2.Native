||| What the runtime asks of the operating system: the OS services, the same
||| on every platform (`Native.Services` says what they are), each a call of
||| the contract's `%extern` for it, wrapped here for the rest of the
||| runtime. A module per platform implements every service, as a record of
||| its functions (`Native.Runtime.OS.LinuxX86_64`), and the native code
||| generator binds each extern, for the platform a program is compiled for,
||| to that platform's function. A service that can fail reports it, 1 for
||| success and 0 for failure, and the caller decides what a failure means.
module Native.Runtime.OS

-- lint: allow public-import: the flat translation reaches through this module
-- (checking an importer's flat functions, it reaches the inline wrappers'
-- bodies, which use the contract's externs, so it is loaded wherever this
-- module is)
import public Native.Services

import Native.Heap

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total


||| End the process with the status.
export %inline
osExit : (status : Bits64) -> Heap.Op Heap ()
osExit = Services.prim__os_exit

||| The standard handles: the output and the errors.
export
stdout, stderr : Bits64
stdout = 1
stderr = 2

||| Write `bytes` at the address to a standard handle; the bytes written.
export %inline
osWrite : (handle, address, bytes : Bits64) -> Heap.Op Heap Bits64
osWrite = Services.prim__os_write

||| Reserve `bytes` of address space, readable by nothing and with no memory
||| committed to it; its address, 0 if the system has none.
export %inline
osReserve : (bytes : Bits64) -> Heap.Op Heap Bits64
osReserve = Services.prim__os_reserve

||| Make `bytes` of reserved whole pages from the address readable,
||| writable and zero; 1 on success.
export %inline
osCommit : (address, bytes : Bits64) -> Heap.Op Heap Bits64
osCommit = Services.prim__os_commit

||| Give `bytes` of committed whole pages from the address back to the
||| system, and reserve them again.
export %inline
osRelease : (address, bytes : Bits64) -> Heap.Op Heap ()
osRelease = Services.prim__os_release

||| The most bytes the process's stack may grow to; 0 if the system does
||| not say.
export %inline
osStackLimit : Heap.Op Heap Bits64
osStackLimit = Services.prim__os_stackLimit

||| The system's page: the bytes it commits and releases memory by.
export %inline
osPageBytes : Heap.Op Heap Bits64
osPageBytes = Services.prim__os_pageBytes

||| Write all `bytes` at the address to a standard handle, in as many writes
||| as it takes; a write that fails ends it, as nothing more would go.
export covering
osWriteAll : (handle, address, bytes : Bits64) -> Heap.Op Heap ()
osWriteAll h a n =
  if n == 0 then Heap.pure () else do
    w <- osWrite h a n
    if w == 0 then Heap.pure () else osWriteAll h (a + w) (n - w)
