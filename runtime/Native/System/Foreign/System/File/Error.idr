||| The foreign functions of `base`'s `System.File.Error`, as the system tier
||| implements them: the last failure as `base`'s file errors read it, a flat
||| function, and whether a file's read or write failed, an ordinary one;
||| each of the foreign one's name and type (`Native.System` says how they
||| are bound).
module Native.System.Foreign.System.File.Error

import Native.Runtime.Ordo as Runtime
import Native.System.Errno
import Native.System.File

%default total

||| `fileError`: 1 once a read or a write of the file failed, 0 before; 1
||| for a closed file.
export covering
prim__error : AnyPtr -> PrimIO Int
prim__error p = toPrim $ File.withFile p 1 (\_, f => do
  e <- File.hasFailed f
  pure (if e then 1 else 0))

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%cg native flat System.Foreign.System.File.Error.prim__fileErrno
||| The last failure as `base`'s `returnError` reads it, as the C support
||| answers: 2 for `ENOENT`, 3 for `EACCES`, 4 for `EEXIST`, and the C
||| library's error number plus 5 for any other (`System.Errno`).
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
