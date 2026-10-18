||| The foreign functions of the prelude's `PrimIO`, as the runtime
||| implements them: each a flat function of the foreign one's name and type
||| (`Native.Support.Foreign.System` says how they are bound).
module Native.Support.Foreign.PrimIO

import Native.Flat.Uniform as Flat
import Native.Runtime.Ordo as Runtime
-- lint: allow import-unused: the flat check reaches through ptrWord's body, which reads raw memory from an object
import Native.Runtime.Raw as Runtime
-- lint: allow import-unused: the flat check reaches through ptrWord's body, which reads raw memory from an object
import Native.Support.Obj
import Native.Support.Ptr
import Native.Types.Represents

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

%cg native flat Support.Foreign.PrimIO.prim__nullAnyPtr
||| 1 for the null pointer, 0 for any other.
export
prim__nullAnyPtr : Flat.Uniform AnyPtr -> Int
prim__nullAnyPtr p = let (Runtime.MkOrdo # r) = nullOp p Runtime.MkOrdo in r
  where
    nullOp : Flat.Uniform AnyPtr -> Runtime.Ordo.Op Runtime.Ordo Int
    nullOp p = do
      w <- Ptr.ptrWord p
      if w == 0 then Runtime.Ordo.pure 1 else Runtime.Ordo.pure 0
