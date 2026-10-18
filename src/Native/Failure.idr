||| Why an OS service failed (`Failure`): the reasons the runtime tells
||| apart, the same on every platform.
|||
||| A service that fails records its reason as the runtime's last failure,
||| a word of its state, by the reason's code (`code`); 0 there means none
||| yet. Each platform's module of the services gives each reason its
||| system reports the failure the runtime knows by, and `Other` to the
||| rest; the support tier gives the libraries' surface the numbers it
||| expects of the C library (`errno`) back.
|||
||| Part of the contract between compiled code and the runtime, with the
||| OS services (`Native.Service`).
module Native.Failure

%default total

||| The reasons an OS service fails.
public export
data Failure
  = ||| Nothing is at the path, or a directory on it is not there.
    NotFound
  | ||| The file's or a directory's permissions forbid it.
    PermissionDenied
  | ||| The operation is not the caller's to make, whatever the permissions.
    NotPermitted
  | ||| Something is at the path already.
    Exists
  | ||| A part of the path that has to be a directory is not one.
    NotADirectory
  | ||| The path is a directory, where it cannot be.
    IsADirectory
  | ||| The directory has entries.
    NotEmpty
  | ||| The file or the directory is in use.
    Busy
  | ||| The process, or the system, has as many files open as it may.
    TooManyOpen
  | ||| The device has no room left.
    NoSpace
  | ||| The file system can only be read.
    ReadOnly
  | ||| The path, or a part of it, is longer than the system takes.
    NameTooLong
  | ||| The path's links lead round in a loop, or are too many.
    LinkLoop
  | ||| The handle is not an open one, or not open for the operation.
    BadHandle
  | ||| An argument is not one the operation takes.
    Invalid
  | ||| A signal came before the operation finished.
    Interrupted
  | ||| The operation would have to wait, and the handle does not.
    WouldBlock
  | ||| The other end of the pipe or the socket is closed.
    BrokenPipe
  | ||| The device failed to read or to write.
    InputOutput
  | ||| The system has no memory for it.
    NoMemory
  | ||| A rename or a link across file systems.
    CrossDevice
  | ||| A reason the runtime does not tell apart.
    Other

||| Each reason's code, the word the runtime's state records it by: from 1,
||| as 0 means no failure.
public export
code : Failure -> Bits64
code NotFound = 1
code PermissionDenied = 2
code NotPermitted = 3
code Exists = 4
code NotADirectory = 5
code IsADirectory = 6
code NotEmpty = 7
code Busy = 8
code TooManyOpen = 9
code NoSpace = 10
code ReadOnly = 11
code NameTooLong = 12
code LinkLoop = 13
code BadHandle = 14
code Invalid = 15
code Interrupted = 16
code WouldBlock = 17
code BrokenPipe = 18
code InputOutput = 19
code NoMemory = 20
code CrossDevice = 21
code Other = 22
