||| The foreign functions of `base`'s `System.Errno`, as the runtime
||| implements them, each a flat function of the foreign one's name and type
||| (`Native.Support.Foreign.System` says how they are bound).
module Native.Support.Foreign.System.Errno

-- lint: allow import-unused: the flat check reaches through lastErrno's body, which compares failures by their codes
import Native.Failure
-- lint: allow import-unused: the flat check reaches through lastErrno's body, which reads the state's raw memory
import Native.Runtime.Memory
import Native.Runtime.Ordo as Runtime
-- lint: allow import-unused: the flat check reaches through lastErrno's body, which reads the state's raw memory
import Native.Runtime.Raw as Runtime
-- lint: allow import-unused: the flat check reaches through lastErrno's body, which reads the runtime's last failure
import Native.Runtime.State
import Native.Support.Errno

%default total

%cg native flat Support.Foreign.System.Errno.prim__getErrno
||| `getErrno`: why the last OS service that failed did, as the C library's
||| error number (`Support.Errno`); 0 if none has.
export
prim__getErrno : PrimIO Int
prim__getErrno w = let (Runtime.MkOrdo # n) = Errno.lastErrno Runtime.MkOrdo in MkIORes (cast n) w
