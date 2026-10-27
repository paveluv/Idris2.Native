-- A module of the runtime's core, by its name, that a test program brings
-- with it: it declares a second extern by the port of the OS service
-- `Exit`, which the runtime's module of the services, `Native.Runtime.OS`,
-- declares already. The code generator binds each service's one extern to
-- the platform's function for it, so a second one is a second binding of
-- `Exit`.
module Native.Runtime.SecondExit

import Native.Runtime.Ordo
import Native.Runtime.PortTy

import Native.HeapObj.Shape
import Native.Port
import Native.Service

%extern service__again : PortTy (Service.port Service.Exit)
