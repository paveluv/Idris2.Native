||| What the runtime asks of the operating system: the OS services, the same
||| on every platform (`Native.Service` says what they are), each a call of
||| an `%extern` declared here, privately, by its service's port, and wrapped
||| for the rest of the runtime. A module per platform implements every
||| service by a function declared by the same port
||| (`Native.Runtime.OS.LinuxX86_64`), and the native code generator binds
||| each extern, for the platform a program is compiled for, to that
||| platform's function. A service that can fail reports it, 1 for success
||| and 0 for failure, and records why as the runtime's last failure
||| (`lastFailure`, a word of `State`); the caller decides what a failure
||| means.
module Native.Runtime.OS

import Native.Runtime.ByteAddr
import Native.Runtime.Ordo
import Native.Runtime.PortTy

import Native.Service

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

%extern service__exit : PortTy (Service.port Service.Exit)
%extern service__write : PortTy (Service.port Service.Write)
%extern service__reserve : PortTy (Service.port Service.Reserve)
%extern service__commit : PortTy (Service.port Service.Commit)
%extern service__release : PortTy (Service.port Service.Release)
%extern service__stackLimit : PortTy (Service.port Service.StackLimit)
%extern service__pageBytes : PortTy (Service.port Service.PageBytes)
%extern service__prepareTerminal : PortTy (Service.port Service.PrepareTerminal)
%extern service__terminalColumns : PortTy (Service.port Service.TerminalColumns)
%extern service__terminalLines : PortTy (Service.port Service.TerminalLines)
%extern service__changeDirectory : PortTy (Service.port Service.ChangeDirectory)
%extern service__currentDirectory : PortTy (Service.port Service.CurrentDirectory)
%extern service__createDirectory : PortTy (Service.port Service.CreateDirectory)
%extern service__removeDirectory : PortTy (Service.port Service.RemoveDirectory)
%extern service__open : PortTy (Service.port Service.Open)
%extern service__close : PortTy (Service.port Service.Close)
%extern service__read : PortTy (Service.port Service.Read)
%extern service__fileSize : PortTy (Service.port Service.FileSize)
%extern service__fileTimes : PortTy (Service.port Service.FileTimes)
%extern service__isTerminal : PortTy (Service.port Service.IsTerminal)
%extern service__removeFile : PortTy (Service.port Service.RemoveFile)
%extern service__readEntry : PortTy (Service.port Service.ReadEntry)

||| End the process with the status.
export %inline
osExit : (status : Bits64) -> Ordo.Op Ordo ()
osExit = service__exit

||| The standard handles: the input, the output and the errors.
export
stdin, stdout, stderr : Bits64
stdin = 0
stdout = 1
stderr = 2

||| The word of all ones, which a service that gives a handle, a count of
||| bytes or a size gives when it fails.
export
failedWord : Bits64
failedWord = 0xFFFFFFFFFFFFFFFF

||| Write `bytes` at the address to a handle; the bytes written, 0 if it
||| fails.
export %inline
osWrite : (handle : Bits64) -> (address : ByteAddr) -> (bytes : Bits64) -> Ordo.Op Ordo Bits64
osWrite = service__write

||| Reserve `bytes` of address space, readable by nothing and with no memory
||| committed to it; its address, the null one if the system has none.
export %inline
osReserve : (bytes : Bits64) -> Ordo.Op Ordo ByteAddr
osReserve = service__reserve

||| Make `bytes` of reserved whole pages from the address readable,
||| writable and zero; 1 on success.
export %inline
osCommit : (address : ByteAddr) -> (bytes : Bits64) -> Ordo.Op Ordo Bits64
osCommit = service__commit

||| Give `bytes` of committed whole pages from the address back to the
||| system, and reserve them again.
export %inline
osRelease : (address : ByteAddr) -> (bytes : Bits64) -> Ordo.Op Ordo ()
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
osChangeDirectory : (path : ByteAddr) -> Ordo.Op Ordo Bits64
osChangeDirectory = service__changeDirectory

||| Write the current directory's path, zero-ended, into the `bytes` at the
||| address; 1 on success, which it is not for a path longer.
export %inline
osCurrentDirectory : (address : ByteAddr) -> (bytes : Bits64) -> Ordo.Op Ordo Bits64
osCurrentDirectory = service__currentDirectory

||| Make a directory at the path, zero-ended bytes at the address, and remove
||| the empty one at it; 1 on success.
export %inline
osCreateDirectory, osRemoveDirectory : (path : ByteAddr) -> Ordo.Op Ordo Bits64
osCreateDirectory = service__createDirectory
osRemoveDirectory = service__removeDirectory

||| Open the file at the path, zero-ended bytes at the address, with the
||| flags (`Native.OpenFlag`); its handle, `failedWord` if it fails.
export %inline
osOpen : (path : ByteAddr) -> (flags : Bits64) -> Ordo.Op Ordo Bits64
osOpen = service__open

||| Close a handle `osOpen` gave; 1 on success.
export %inline
osClose : (handle : Bits64) -> Ordo.Op Ordo Bits64
osClose = service__close

||| Read at most `bytes` from the handle into the bytes at the address;
||| the bytes read, 0 at the end, `failedWord` if it fails.
export %inline
osRead : (handle : Bits64) -> (address : ByteAddr) -> (bytes : Bits64) -> Ordo.Op Ordo Bits64
osRead = service__read

||| The bytes of the handle's file; `failedWord` if it fails.
export %inline
osFileSize : (handle : Bits64) -> Ordo.Op Ordo Bits64
osFileSize = service__fileSize

||| The times of the handle's file written into six words at the address:
||| its last access, modification and change of status, each seconds then
||| nanoseconds; 1 on success.
export %inline
osFileTimes : (handle : Bits64) -> (address : ByteAddr) -> Ordo.Op Ordo Bits64
osFileTimes = service__fileTimes

||| Whether the handle is a terminal's: 1 if it is.
export %inline
osIsTerminal : (handle : Bits64) -> Ordo.Op Ordo Bits64
osIsTerminal = service__isTerminal

||| Remove the file at the path, zero-ended bytes at the address, which is
||| not a directory; 1 on success.
export %inline
osRemoveFile : (path : ByteAddr) -> Ordo.Op Ordo Bits64
osRemoveFile = service__removeFile

||| The next entry of a directory `osOpen` gave with `ADirectory`: its
||| name written, zero-ended, into the `bytes` at the address, 256 enough;
||| the name's bytes, 0 when there are no more, `failedWord` if it fails.
export %inline
osReadEntry : (handle : Bits64) -> (address : ByteAddr) -> (bytes : Bits64) -> Ordo.Op Ordo Bits64
osReadEntry = service__readEntry

||| Write all `bytes` at the address to a handle, in as many writes as it
||| takes; whether they all went, as a write that fails ends it.
export covering
osWriteAll : (handle : Bits64) -> (address : ByteAddr) -> (bytes : Bits64) -> Ordo.Op Ordo Bool
osWriteAll h a n =
  if n == 0 then Ordo.pure True else do
    w <- osWrite h a n
    if w == 0 then Ordo.pure False else osWriteAll h (ByteAddr.offset a w) (n - w)
