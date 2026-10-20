||| The foreign functions of the prelude's `Prelude.IO`, as the runtime
||| implements them: each a flat function of the foreign one's name and type
||| (`Native.Support` says how they are bound). A string is
||| the system's text through `Support.Text`, for every encoding.
module Native.Support.Foreign.Prelude.IO

import Native.Flat.Uniform as Flat
import Native.Runtime.Ordo as Runtime
import Native.Runtime.Raw as Runtime
import Native.Support.Obj
import Native.Support.Ptr
import Native.Support.Text
import Native.Types.Kind
import Native.Types.Represents

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

%cg native flat Support.Foreign.Prelude.IO.prim__getString
||| `getString`: the string a pointer is, if it is one of the heap
||| (`Support.Ptr`), itself; else the zero-ended text it points to, copied;
||| the empty string for the null pointer, which the C library would read
||| through. The program ends for a handle, which points to no text.
export covering
prim__getString : Flat.Uniform (Ptr String) -> Flat.Uniform String
prim__getString p = let (Runtime.MkOrdo # r) = getOp Runtime.MkOrdo in r
  where
    covering
    getOp : Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform String)
    getOp = do
      target <- Ptr.pointee p
      case target of
        HeapString s => Obj.objectValue s
        Address a => if Runtime.Raw.isNull a then Text.emptyText else Text.zeroEndedText a
        Handle _ => Runtime.Ordo.crashOp "idris: getString of a handle, which points to no text"
