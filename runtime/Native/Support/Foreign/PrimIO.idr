||| The foreign functions of the prelude's `PrimIO`, as the runtime
||| implements them: each a flat function of the foreign one's name and type
||| (`Native.Support` says how they are bound).
module Native.Support.Foreign.PrimIO

import Native.Flat.Uniform as Flat
import Native.Runtime.Ordo as Runtime
import Native.Runtime.Raw as Runtime
import Native.Support.Ptr
import Native.Types.Represents

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

%cg native flat Support.Foreign.PrimIO.prim__nullAnyPtr
||| 1 for the null pointer, 0 for any other: an object of the heap given for
||| a pointer (`Support.Ptr`) is never null, nor is a handle.
export
prim__nullAnyPtr : Flat.Uniform AnyPtr -> Int
prim__nullAnyPtr p = let (Runtime.MkOrdo # r) = nullOp p Runtime.MkOrdo in r
  where
    nullOp : Flat.Uniform AnyPtr -> Runtime.Ordo.Op Runtime.Ordo Int
    nullOp p = do
      target <- Ptr.pointee p
      case target of
        Ptr.Address a => Runtime.Ordo.pure (if Runtime.Raw.isNull a then 1 else 0)
        Ptr.HeapString _ => Runtime.Ordo.pure 0
        Ptr.Handle _ => Runtime.Ordo.pure 0
