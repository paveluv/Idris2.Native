||| The runtime's last failure as the C library's error number (`errno`),
||| which `base`'s surface expects: `getErrno` answers it, and the file
||| errors are read from it.
|||
||| The numbers are those Linux gives, which the POSIX systems share for
||| the older errors (`ENOENT` 2, `EACCES` 13, `EEXIST` 17). A reason the
||| runtime does not tell apart is `EIO`, an input or output error; no
||| failure yet is 0.
module Native.System.Errno

import Native.Failure
import Native.Runtime.Ordo as Runtime
import Native.Runtime.State

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| The C library's number for a reason's code (`Native.Failure`).
export
errnoOf : (code : Bits64) -> Bits64
errnoOf c =
  if c == 0 then 0
  else if c == Failure.code Failure.NotFound then 2 -- ENOENT
  else if c == Failure.code Failure.PermissionDenied then 13 -- EACCES
  else if c == Failure.code Failure.NotPermitted then 1 -- EPERM
  else if c == Failure.code Failure.Exists then 17 -- EEXIST
  else if c == Failure.code Failure.NotADirectory then 20 -- ENOTDIR
  else if c == Failure.code Failure.IsADirectory then 21 -- EISDIR
  else if c == Failure.code Failure.NotEmpty then 39 -- ENOTEMPTY
  else if c == Failure.code Failure.Busy then 16 -- EBUSY
  else if c == Failure.code Failure.TooManyOpen then 24 -- EMFILE
  else if c == Failure.code Failure.NoSpace then 28 -- ENOSPC
  else if c == Failure.code Failure.ReadOnly then 30 -- EROFS
  else if c == Failure.code Failure.NameTooLong then 36 -- ENAMETOOLONG
  else if c == Failure.code Failure.LinkLoop then 40 -- ELOOP
  else if c == Failure.code Failure.BadHandle then 9 -- EBADF
  else if c == Failure.code Failure.Invalid then 22 -- EINVAL
  else if c == Failure.code Failure.Interrupted then 4 -- EINTR
  else if c == Failure.code Failure.WouldBlock then 11 -- EAGAIN
  else if c == Failure.code Failure.BrokenPipe then 32 -- EPIPE
  else if c == Failure.code Failure.NoMemory then 12 -- ENOMEM
  else if c == Failure.code Failure.CrossDevice then 18 -- EXDEV
  else 5 -- EIO: InputOutput, Other

||| The C library's number for the runtime's last failure.
export
lastErrno : Runtime.Ordo.Op Runtime.Ordo Bits64
lastErrno = do
  c <- Runtime.State.getState Runtime.State.lastFailure
  Runtime.Ordo.pure (errnoOf c)
