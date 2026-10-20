||| The foreign functions of `base`'s `System.Errno`, as the system tier
||| implements them, each a flat function of the foreign one's name and type
||| (`Native.System` says how they are bound).
module Native.System.Foreign.System.Errno

import Native.Flat.Uniform as Flat
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

%cg native flat System.Foreign.System.Errno.prim__strerror
||| `strerror`: the C library's message for the error number
||| (`System.ErrorMessage`).
export covering
prim__strerror : Int -> PrimIO (Flat.Uniform String)
prim__strerror n w = let (Runtime.MkOrdo # s) =
                           ErrorMessage.errorMessage n Runtime.MkOrdo in MkIORes s w
