||| The OS services (`Service`): what the runtime asks of the operating
||| system, the same on every platform.
|||
||| This module is the contract for them, and the only place it is stated:
||| which services there are, and each one's arrow (`port`). The runtime's
||| module of the services declares an extern for each by its port
||| (`%extern service__write : PortTy (port Write)` in
||| `Native.Runtime.OS`), through which the rest of the runtime calls it;
||| each platform's module implements every service by a function declared
||| by the same port (`write : PortTy (port Write)` in
||| `Native.Runtime.OS.LinuxX86_64`). Idris checks both against the port;
||| for the platform a program is compiled for, the code generator finds
||| both by their types, and binds the extern to the function. A service
||| that can fail reports whether it succeeded (a `Mach.Bool`), and records
||| why as the runtime's last failure (`Native.Failure`); the caller
||| decides what a failure means.
|||
||| Part of the contract between compiled code and the runtime, with the
||| heap-object model (`HeapObj.Shape` says what it is).
module Native.Service

import Native.Carrier
import Native.Field
import Native.Mach
import Native.Port

import Data.List.Elem

%default total

||| The OS services.
public export
data Service
  = ||| End the process with the status.
    Exit
  | ||| Write the bytes at an address to a handle, a standard one (1 the
    ||| output, 2 the errors) or one `Open` gave; the bytes written, 0 if
    ||| it fails.
    Write
  | ||| Reserve address space, readable by nothing, which no memory is
    ||| committed to; its address, the null one if there is none.
    Reserve
  | ||| Make reserved whole pages at an address readable and writable, and
    ||| zero; success.
    Commit
  | ||| Give committed whole pages back and reserve them again.
    Release
  | ||| The most bytes the process's stack may grow to, 0 if the system does
    ||| not say.
    StackLimit
  | ||| The system's page, the bytes memory is committed and released by.
    PageBytes
  | ||| Make the terminal of the output take the escape sequences that move
    ||| the cursor and colour text, where the system has to be asked.
    PrepareTerminal
  | ||| The columns of the terminal the standard input is, or else the
    ||| standard output; 0 if neither is a terminal.
    TerminalColumns
  | ||| The lines of the terminal the standard input is, or else the
    ||| standard output; 0 if neither is a terminal.
    TerminalLines
  | ||| Make the directory of a path, zero-ended bytes at an address, the
    ||| current one; success.
    ChangeDirectory
  | ||| Write the current directory's path, zero-ended, into the bytes at an
    ||| address, at most so many; success, which it is not for a path longer.
    CurrentDirectory
  | ||| Make a directory at a path, zero-ended bytes at an address, with the
    ||| permissions the system gives a new one; success.
    CreateDirectory
  | ||| Remove the directory at a path, zero-ended bytes at an address, which
    ||| has to be empty; success.
    RemoveDirectory
  | ||| Open the file at a path, zero-ended bytes at an address, with the
    ||| flags (`Native.OpenFlag`); its handle, the word of all ones if it
    ||| fails. A file made has the permissions the system gives a new one.
    Open
  | ||| Close a handle `Open` gave; success.
    Close
  | ||| Read bytes from a handle, a standard one (0 the input) or one `Open`
    ||| gave, into the bytes at an address, at most so many; the bytes
    ||| read, 0 at the end, the word of all ones if it fails.
    Read
  | ||| The bytes of the file of a handle; the word of all ones if it fails.
    FileSize
  | ||| The times of the file of a handle, written into six words at an
    ||| address: its last access, its last modification and its last change
    ||| of status, each its seconds since the epoch, then the nanoseconds
    ||| past them; success.
    FileTimes
  | ||| Whether a handle is a terminal's.
    IsTerminal
  | ||| Remove the file at a path, zero-ended bytes at an address, which is
    ||| not a directory; success.
    RemoveFile
  | ||| Give the file at a path, zero-ended bytes at an address, the
    ||| permissions of a mode, its low twelve bits as the system reads them
    ||| (the owner's, the group's and the others', and the set-user-id,
    ||| set-group-id and sticky bits); success.
    ChangeMode
  | ||| The next entry of a directory `Open` gave with `ADirectory`: its name
    ||| written, zero-ended, into the bytes at an address, at most so many,
    ||| 256 enough on every platform; the name's bytes, 0 when there are no
    ||| more, the word of all ones if it fails. The entries `.` and `..` are
    ||| among them, where the system has them.
    ReadEntry

||| Each service's arrow: what its arguments and its result carry.
public export
port : Service -> Port
port Exit = "status" ~: Mach.U64 ~> ()
port Write =
  "handle" ~: Mach.U64 ~> "bytes" ~: Carrier.ByteAddr ~> "count" ~: Mach.U64
    ~> "written" ~: Mach.U64
port Reserve = "bytes" ~: Mach.U64 ~> "space" ~: Carrier.ByteAddr
port Commit = "pages" ~: Carrier.ByteAddr ~> "bytes" ~: Mach.U64 ~> "ok" ~: Mach.Bool
port Release = "pages" ~: Carrier.ByteAddr ~> "bytes" ~: Mach.U64 ~> ()
port StackLimit = () ~> "bytes" ~: Mach.U64
port PageBytes = () ~> "bytes" ~: Mach.U64
port PrepareTerminal = () ~> ()
port TerminalColumns = () ~> "columns" ~: Mach.U64
port TerminalLines = () ~> "lines" ~: Mach.U64
port ChangeDirectory = "path" ~: Carrier.ByteAddr ~> "ok" ~: Mach.Bool
port CurrentDirectory = "into" ~: Carrier.ByteAddr ~> "most" ~: Mach.U64 ~> "ok" ~: Mach.Bool
port CreateDirectory = "path" ~: Carrier.ByteAddr ~> "ok" ~: Mach.Bool
port RemoveDirectory = "path" ~: Carrier.ByteAddr ~> "ok" ~: Mach.Bool
port Open = "path" ~: Carrier.ByteAddr ~> "flags" ~: Mach.U64 ~> "handle" ~: Mach.U64
port Close = "handle" ~: Mach.U64 ~> "ok" ~: Mach.Bool
port Read =
  "handle" ~: Mach.U64 ~> "into" ~: Carrier.ByteAddr ~> "most" ~: Mach.U64
    ~> "read" ~: Mach.U64
port FileSize = "handle" ~: Mach.U64 ~> "bytes" ~: Mach.U64
port FileTimes = "handle" ~: Mach.U64 ~> "into" ~: Carrier.ByteAddr ~> "ok" ~: Mach.Bool
port IsTerminal = "handle" ~: Mach.U64 ~> "terminal" ~: Mach.Bool
port RemoveFile = "path" ~: Carrier.ByteAddr ~> "ok" ~: Mach.Bool
port ChangeMode = "path" ~: Carrier.ByteAddr ~> "mode" ~: Mach.U64 ~> "ok" ~: Mach.Bool
port ReadEntry =
  "handle" ~: Mach.U64 ~> "into" ~: Carrier.ByteAddr ~> "most" ~: Mach.U64
    ~> "bytes" ~: Mach.U64

||| Every service, once. The code generator pairs this list's term, as the
||| loaded runtime's context holds it, with its own copy, element by element.
public export
allServices : List Service
allServices =
  [ Exit, Write, Reserve, Commit, Release, StackLimit, PageBytes, PrepareTerminal, TerminalColumns
  , TerminalLines, ChangeDirectory, CurrentDirectory, CreateDirectory, RemoveDirectory, Open, Close
  , Read, FileSize, FileTimes, IsTerminal, RemoveFile, ChangeMode, ReadEntry ]

||| The list holds every service.
complete : (c : Service) -> Elem c Service.allServices
complete Exit = %search
complete Write = %search
complete Reserve = %search
complete Commit = %search
complete Release = %search
complete StackLimit = %search
complete PageBytes = %search
complete PrepareTerminal = %search
complete TerminalColumns = %search
complete TerminalLines = %search
complete ChangeDirectory = %search
complete CurrentDirectory = %search
complete CreateDirectory = %search
complete RemoveDirectory = %search
complete Open = %search
complete Close = %search
complete Read = %search
complete FileSize = %search
complete FileTimes = %search
complete IsTerminal = %search
complete RemoveFile = %search
complete ChangeMode = %search
complete ReadEntry = %search
