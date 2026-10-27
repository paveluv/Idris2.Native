||| The foreign functions of `base`'s `System.Errno`, as the system tier
||| implements them, each a function of the foreign one's name and type
||| (`Native.System` says how they are bound): `getErrno` a flat one, which
||| reads the runtime's last failure, and `strerror` an ordinary one.
module Native.System.Foreign.System.Errno

import Native.Runtime.Ordo as Runtime
import Native.System.Errno
import Native.System.ErrorMessage

%default total

%cg native flat System.Foreign.System.Errno.prim__getErrno
||| `getErrno`: why the last OS service that failed did, as the C library's
||| error number (`System.Errno`); 0 if none has.
export
prim__getErrno : PrimIO Int
prim__getErrno w = let (Runtime.MkOrdo # n) = Errno.lastErrno Runtime.MkOrdo in MkIORes (cast n) w

||| `strerror`: the C library's message for the error number
||| (`System.ErrorMessage`), compiled with the program, as its messages are
||| string literals, which ordinary code holds as static strings.
export
prim__strerror : Int -> PrimIO String
prim__strerror n w = MkIORes (ErrorMessage.errorMessage n) w
