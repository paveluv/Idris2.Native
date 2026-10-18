||| What the runtime asks of the operating system: the OS services, the same
||| on every platform (`Native.Service` says what they are), each a call of
||| an `%extern` declared here, privately, by its service's port, and wrapped
||| for the rest of the runtime. A module per platform implements every
||| service by a function declared by the same port
||| (`Native.Runtime.OS.LinuxX86_64`), and the native code generator binds
||| each extern, for the platform a program is compiled for, to that
||| platform's function. A service that can fail reports it, 1 for success
||| and 0 for failure, and records why as the runtime's last failure
||| (`State.lastFailure`); the caller decides what a failure means.
module Native.Runtime.OS

-- lint: allow public-import: an extern's type, written by its port, reduces only
-- where the port and its reading are visible, so they are wherever this
-- module is, whose wrappers the flat translation unfolds into its importers
import public Native.Port
import public Native.Runtime.PortTy
import public Native.Service

import Native.Runtime.Ordo
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
%extern service__prepareTerminal : PortTy.ExternTy (Service.port Service.PrepareTerminal)
%extern service__terminalColumns : PortTy.ExternTy (Service.port Service.TerminalColumns)
%extern service__terminalLines : PortTy.ExternTy (Service.port Service.TerminalLines)
%extern service__changeDirectory : PortTy.ExternTy (Service.port Service.ChangeDirectory)
%extern service__currentDirectory : PortTy.ExternTy (Service.port Service.CurrentDirectory)
%extern service__createDirectory : PortTy.ExternTy (Service.port Service.CreateDirectory)
%extern service__removeDirectory : PortTy.ExternTy (Service.port Service.RemoveDirectory)


||| End the process with the status.
export %inline
osExit : (status : Bits64) -> Ordo.Op Ordo ()
osExit = service__exit

||| The standard handles: the output and the errors.
export
stdout, stderr : Bits64
stdout = 1
stderr = 2

||| Write `bytes` at the address to a standard handle; the bytes written.
export %inline
osWrite : (handle : Bits64) -> (address : Raw) -> (bytes : Bits64) -> Ordo.Op Ordo Bits64
osWrite = service__write

||| Reserve `bytes` of address space, readable by nothing and with no memory
||| committed to it; its address, the null one if the system has none.
export %inline
osReserve : (bytes : Bits64) -> Ordo.Op Ordo Raw
osReserve = service__reserve

||| Make `bytes` of reserved whole pages from the address readable,
||| writable and zero; 1 on success.
export %inline
osCommit : (address : Raw) -> (bytes : Bits64) -> Ordo.Op Ordo Bits64
osCommit = service__commit

||| Give `bytes` of committed whole pages from the address back to the
||| system, and reserve them again.
export %inline
osRelease : (address : Raw) -> (bytes : Bits64) -> Ordo.Op Ordo ()
osRelease = service__release

||| The most bytes the process's stack may grow to; 0 if the system does
||| not say.
export %inline
osStackLimit : Ordo.Op Ordo Bits64
osStackLimit = service__stackLimit

||| The system's page: the bytes it commits and releases memory by.
export %inline
osPageBytes : Ordo.Op Ordo Bits64
osPageBytes = service__pageBytes

||| Make the terminal of the output take the escape sequences that move the
||| cursor and colour text, where the system has to be asked.
export %inline
osPrepareTerminal : Ordo.Op Ordo ()
osPrepareTerminal = service__prepareTerminal

||| The columns and the lines of the terminal the standard input is, or else
||| the standard output; 0 if neither is a terminal.
export %inline
osTerminalColumns, osTerminalLines : Ordo.Op Ordo Bits64
osTerminalColumns = service__terminalColumns
osTerminalLines = service__terminalLines

||| Make the directory of the path, zero-ended bytes at the address, the
||| current one; 1 on success.
export %inline
osChangeDirectory : (path : Raw) -> Ordo.Op Ordo Bits64
osChangeDirectory = service__changeDirectory

||| Write the current directory's path, zero-ended, into the `bytes` at the
||| address; 1 on success, which it is not for a path longer.
export %inline
osCurrentDirectory : (address : Raw) -> (bytes : Bits64) -> Ordo.Op Ordo Bits64
osCurrentDirectory = service__currentDirectory

||| Make a directory at the path, zero-ended bytes at the address, and remove
||| the empty one at it; 1 on success.
export %inline
osCreateDirectory, osRemoveDirectory : (path : Raw) -> Ordo.Op Ordo Bits64
osCreateDirectory = service__createDirectory
osRemoveDirectory = service__removeDirectory

||| Write all `bytes` at the address to a standard handle, in as many writes
||| as it takes; a write that fails ends it, as nothing more would go.
export covering
osWriteAll : (handle : Bits64) -> (address : Raw) -> (bytes : Bits64) -> Ordo.Op Ordo ()
osWriteAll h a n =
  if n == 0 then Ordo.pure () else do
    w <- osWrite h a n
    if w == 0 then Ordo.pure () else osWriteAll h (Raw.offset a w) (n - w)
