||| The runtime's externs, each named by its contract: `intrinsic__load` by an
||| intrinsic's port and `service__exit` by a service's pass; `prim__store`,
||| a primitive's prefix on an intrinsic, and `service__peek`, a service's
||| prefix on an intrinsic, are reported (`extern-name`).
module Native.Runtime.Named

%default total

%extern intrinsic__load : ExternTy (Intrinsic.port Intrinsic.Load64)
%extern service__exit : ExternTy (Service.port Service.Exit)
%extern prim__store : ExternTy (Intrinsic.port Intrinsic.Store64)
%extern service__peek : ExternTy (Intrinsic.port Intrinsic.Load8)
