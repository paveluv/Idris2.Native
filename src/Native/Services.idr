||| The OS services (`Services`): what the runtime asks of the operating
||| system, the same on every platform.
|||
||| The generic runtime calls a service through its `%extern` here, of the
||| contract; each platform's module of the runtime implements every
||| service, as a record of its functions (`services` in
||| `Native.Runtime.OS.LinuxX86_64`) that Idris checks against the ports.
||| For the platform a program is compiled for, the code generator binds
||| each extern of `externs` to the function in the same field of that
||| platform's record. A service that can fail reports it, 1 for success
||| and 0 for failure, and the caller decides what a failure means. Only
||| the runtime's module of the services imports this one (the linter's
||| `services`).
|||
||| Part of the contract between compiled code and the runtime, with the
||| heap-object model (`HeapObj.Shape` says what it is).
module Native.Services

import Native.Heap
import Native.HeapObj.Shape as HeapObj
import Native.Port

%default total

export
%extern prim__os_exit : (status : Bits64) -> (1 m : Heap) -> Heap.Ret Heap ()
export
%extern prim__os_write : (handle, address, bytes : Bits64) -> (1 m : Heap) -> Heap.Ret Heap Bits64
export
%extern prim__os_reserve : (bytes : Bits64) -> (1 m : Heap) -> Heap.Ret Heap Bits64
export
%extern prim__os_commit : (address, bytes : Bits64) -> (1 m : Heap) -> Heap.Ret Heap Bits64
export
%extern prim__os_release : (address, bytes : Bits64) -> (1 m : Heap) -> Heap.Ret Heap ()
export
%extern prim__os_stackLimit : (1 m : Heap) -> Heap.Ret Heap Bits64
export
%extern prim__os_pageBytes : (1 m : Heap) -> Heap.Ret Heap Bits64

||| The OS services, each a field of its port.
public export
record Services (f : Port -> Type) where
  constructor MkServices
  ||| End the process with the status.
  exit : f (MkPort [Port.Word] Nothing)
  ||| Write the bytes at an address to a standard handle (1 the output, 2
  ||| the errors); the bytes written.
  write : f (MkPort [Port.Word, Port.Word, Port.Word] (Just Port.Word))
  ||| Reserve address space, readable by nothing, which no memory is
  ||| committed to; its address, 0 if there is none.
  reserve : f (MkPort [Port.Word] (Just Port.Word))
  ||| Make reserved whole pages at an address readable and writable, and
  ||| zero; success.
  commit : f (MkPort [Port.Word, Port.Word] (Just Port.Word))
  ||| Give committed whole pages back and reserve them again.
  release : f (MkPort [Port.Word, Port.Word] Nothing)
  ||| The most bytes the process's stack may grow to, 0 if the system does
  ||| not say.
  stackLimit : f (MkPort [] (Just Port.Word))
  ||| The system's page, the bytes memory is committed and released by.
  pageBytes : f (MkPort [] (Just Port.Word))

||| The services' externs, each checked against its field's port.
public export
externs : Services Port.ExternTy
externs =
  MkServices
    { exit = prim__os_exit, write = prim__os_write, reserve = prim__os_reserve, commit = prim__os_commit
    , release = prim__os_release, stackLimit = prim__os_stackLimit, pageBytes = prim__os_pageBytes }

||| Each service's entries of two records made one.
public export
zipServices : ({p : Port} -> f p -> g p -> h p) -> Services f -> Services g -> Services h
zipServices z a b =
  MkServices (z a.exit b.exit) (z a.write b.write) (z a.reserve b.reserve) (z a.commit b.commit)
    (z a.release b.release) (z a.stackLimit b.stackLimit) (z a.pageBytes b.pageBytes)

||| The services' entries, each with its port.
public export
serviceList : Services f -> List (p : Port ** f p)
serviceList r =
  [ (_ ** r.exit), (_ ** r.write), (_ ** r.reserve), (_ ** r.commit), (_ ** r.release)
  , (_ ** r.stackLimit), (_ ** r.pageBytes) ]
