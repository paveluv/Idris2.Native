||| The OS services (`Service`): what the runtime asks of the operating
||| system, the same on every platform.
|||
||| This module is the contract for them, and the only place it is stated:
||| which services there are, and each one's arrow (`port`). The runtime's
||| module of the services declares an extern for each by its port
||| (`%extern service__write : ExternTy (port Write)` in
||| `Native.Runtime.OS`), through which the rest of the runtime calls it;
||| each platform's module implements every service by a function declared
||| by the same port (`write : PortTy Memory.Addr (port Write)` in
||| `Native.Runtime.OS.LinuxX86_64`). Idris checks both against the port;
||| for the platform a program is compiled for, the code generator finds
||| both by their types, and binds the extern to the function. A service
||| that can fail reports it, 1 for success and 0 for failure, and the
||| caller decides what a failure means.
|||
||| Part of the contract between compiled code and the runtime, with the
||| heap-object model (`HeapObj.Shape` says what it is).
module Native.Service

import Native.Port

import Data.List.Elem

%default total

||| The OS services.
public export
data Service
  = ||| End the process with the status.
    Exit
  | ||| Write the bytes at an address to a standard handle (1 the output, 2
    ||| the errors); the bytes written.
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

||| Each service's arrow: what its arguments and its result carry.
public export
port : Service -> Port
port Exit = MkPort [Port.Word] Nothing
port Write = MkPort [Port.Word, Port.Raw, Port.Word] (Just Port.Word)
port Reserve = MkPort [Port.Word] (Just Port.Raw)
port Commit = MkPort [Port.Raw, Port.Word] (Just Port.Word)
port Release = MkPort [Port.Raw, Port.Word] Nothing
port StackLimit = MkPort [] (Just Port.Word)
port PageBytes = MkPort [] (Just Port.Word)

||| Every service, once. The code generator pairs this list's term, as the
||| loaded runtime's context holds it, with its own copy, element by element.
public export
allServices : List Service
allServices = [Exit, Write, Reserve, Commit, Release, StackLimit, PageBytes]

||| The list holds every service.
export
complete : (c : Service) -> Elem c Service.allServices
complete Exit = Here
complete Write = There (Here)
complete Reserve = There (There (Here))
complete Commit = There (There (There (Here)))
complete Release = There (There (There (There (Here))))
complete StackLimit = There (There (There (There (There (Here)))))
complete PageBytes = There (There (There (There (There (There (Here))))))
