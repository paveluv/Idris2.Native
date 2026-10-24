||| The foreign function of `base`'s `System.File.Permissions`, as the
||| system tier implements it, a flat function of the foreign one's name and
||| type (`Native.System` says how they are bound).
module Native.System.Foreign.System.File.Permissions

import Native.Flat.Uniform as Flat
import Native.Runtime.ByteAddr as Runtime
import Native.Runtime.Ordo as Runtime
import Native.Runtime.OS
import Native.Support.Text

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

%cg native flat System.Foreign.System.File.Permissions.prim__chmod
||| `chmod`: the file at the path given the permissions of the mode; 0 when
||| it is, -1 when it is not or there is no memory for the path, as the C
||| library's `chmod` answers, the reason the last failure.
export covering
prim__chmod : Flat.Uniform String -> Int -> PrimIO Int
prim__chmod path mode w = let (Runtime.MkOrdo # r) = op Runtime.MkOrdo in MkIORes r w
  where
    covering
    op : Runtime.Ordo.Op Runtime.Ordo Int
    op = Support.Text.withPath path (Runtime.Ordo.pure (-1)) (\p => do
      ok <- Runtime.OS.osChangeMode p (cast mode)
      Runtime.Ordo.pure (if ok then 0 else -1))
