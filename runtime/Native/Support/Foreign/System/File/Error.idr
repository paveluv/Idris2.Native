||| The foreign functions of `base`'s `System.File.Error`, as the runtime
||| implements them, each a flat function of the foreign one's name and type
||| (`Native.Support.Foreign.System` says how they are bound).
module Native.Support.Foreign.System.File.Error

import Native.Runtime.Ordo as Runtime
import Native.Support.Errno

%default total

%cg native flat Support.Foreign.System.File.Error.prim__fileErrno
||| The last failure as `base`'s `returnError` reads it, as the C support
||| answers: 2 for `ENOENT`, 3 for `EACCES`, 4 for `EEXIST`, and the C
||| library's error number plus 5 for any other (`Support.Errno`).
export
prim__fileErrno : PrimIO Int
prim__fileErrno w = let (Runtime.MkOrdo # n) =
                          Errno.lastErrno Runtime.MkOrdo in MkIORes (fileErrno (cast n)) w
  where
    fileErrno : Int -> Int
    fileErrno 2 = 2
    fileErrno 13 = 3
    fileErrno 17 = 4
    fileErrno e = e + 5
