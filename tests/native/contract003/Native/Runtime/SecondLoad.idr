-- A module of the runtime's core, by its name, that a test program brings
-- with it: it declares a second inline extern by the port of `Load64`,
-- which the runtime's `Native.Runtime.Memory` declares already. An extern
-- is a declaration with no body, and its type, the port, says which
-- intrinsic it is:
--
--     %extern intrinsic__load64 : PortTy (Intrinsic.port Intrinsic.Load64)
--
-- is the runtime's, and the one below is this module's.
module Native.Runtime.SecondLoad

import Native.Runtime.ByteAddr
import Native.Runtime.Ordo
import Native.Runtime.PortTy

import Native.HeapObj.Shape
import Native.Intrinsic
import Native.Port

%extern intrinsic__again : PortTy (Intrinsic.port Intrinsic.Load64)
