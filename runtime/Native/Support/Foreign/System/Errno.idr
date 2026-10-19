||| The foreign functions of `base`'s `System.Errno`, as the runtime
||| implements them, each a flat function of the foreign one's name and type
||| (`Native.Support.Foreign.System` says how they are bound).
module Native.Support.Foreign.System.Errno

import Native.Runtime.Ordo as Runtime
import Native.Support.Errno

%default total

%cg native flat Support.Foreign.System.Errno.prim__getErrno
||| `getErrno`: why the last OS service that failed did, as the C library's
||| error number (`Support.Errno`); 0 if none has.
export
prim__getErrno : PrimIO Int
prim__getErrno w = let (Runtime.MkOrdo # n) = Errno.lastErrno Runtime.MkOrdo in MkIORes (cast n) w
