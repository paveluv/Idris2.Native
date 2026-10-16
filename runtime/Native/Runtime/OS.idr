||| What the runtime asks of the operating system: the OS services, the same
||| on every platform (`Native.Services` says what they are), each a call of
||| an `%extern` for it, declared here, privately, and wrapped for the rest
||| of the runtime; `externs` is the record of them, checked against the
||| ports, which the code generator reads. A module per platform implements every service, as a record of
||| its functions (`Native.Runtime.OS.LinuxX86_64`), and the native code
||| generator binds each extern, for the platform a program is compiled for,
||| to that platform's function. A service that can fail reports it, 1 for
||| success and 0 for failure, and the caller decides what a failure means.
module Native.Runtime.OS

import Native.Runtime.Heap
import Native.Runtime.PortTy
import Native.Runtime.Raw

-- lint: allow import-unused: the record's fields unfold to its ports' types, which
-- Idris compares with the record's entries only where `Native.Port` is imported
import Native.Port
import Native.Services

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

%extern prim__os_exit : (status : Bits64) -> (1 m : Heap) -> Heap.Ret Heap ()
%extern prim__os_write : (handle : Bits64) -> (address : Raw) -> (bytes : Bits64) -> (1 m : Heap) -> Heap.Ret Heap Bits64
%extern prim__os_reserve : (bytes : Bits64) -> (1 m : Heap) -> Heap.Ret Heap Raw
%extern prim__os_commit : (address : Raw) -> (bytes : Bits64) -> (1 m : Heap) -> Heap.Ret Heap Bits64
%extern prim__os_release : (address : Raw) -> (bytes : Bits64) -> (1 m : Heap) -> Heap.Ret Heap ()
%extern prim__os_stackLimit : (1 m : Heap) -> Heap.Ret Heap Bits64
%extern prim__os_pageBytes : (1 m : Heap) -> Heap.Ret Heap Bits64

||| The services' externs, each checked against its field's port: what the
||| code generator binds, for a program's platform, to that platform's
||| functions.
export
externs : Services PortTy.ExternTy
externs =
  MkServices
    { exit = prim__os_exit, write = prim__os_write, reserve = prim__os_reserve, commit = prim__os_commit
    , release = prim__os_release, stackLimit = prim__os_stackLimit, pageBytes = prim__os_pageBytes }


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
osWrite : (handle : Bits64) -> (address : Raw) -> (bytes : Bits64) -> Heap.Op Heap Bits64
osWrite = prim__os_write

||| Reserve `bytes` of address space, readable by nothing and with no memory
||| committed to it; its address, the null one if the system has none.
export %inline
osReserve : (bytes : Bits64) -> Heap.Op Heap Raw
osReserve = prim__os_reserve

||| Make `bytes` of reserved whole pages from the address readable,
||| writable and zero; 1 on success.
export %inline
osCommit : (address : Raw) -> (bytes : Bits64) -> Heap.Op Heap Bits64
osCommit = prim__os_commit

||| Give `bytes` of committed whole pages from the address back to the
||| system, and reserve them again.
export %inline
osRelease : (address : Raw) -> (bytes : Bits64) -> Heap.Op Heap ()
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

||| Write all `bytes` at the address to a standard handle, in as many writes
||| as it takes; a write that fails ends it, as nothing more would go.
export covering
osWriteAll : (handle : Bits64) -> (address : Raw) -> (bytes : Bits64) -> Heap.Op Heap ()
osWriteAll h a n =
  if n == 0 then Heap.pure () else do
    w <- osWrite h a n
    if w == 0 then Heap.pure () else osWriteAll h (Raw.offset a w) (n - w)
