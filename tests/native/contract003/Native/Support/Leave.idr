-- A module of the runtime's support tier, by its name, that a test program
-- brings with it: it declares a second extern by the port of the OS
-- service `Exit`, which the runtime's module of the services declares
-- already,
--
--     %extern service__exit : PortTy (Service.port Service.Exit)
--
-- in `Native.Runtime.OS`. The runtime declares its externs only in its
-- core and in `Native.Support.Text`, and the code generator looks for an
-- extern of the contract only there: this one it would not find, so it
-- would be an ordinary extern, with no service bound to it, and each call
-- of it would fail as it ran. So the module's build refuses it, at the
-- extern, before any program is compiled with it.
module Native.Support.Leave

import Native.HeapObj.Shape
import Native.Port
import Native.Runtime.Ordo
import Native.Runtime.PortTy
import Native.Service

%extern service__leave : PortTy (Service.port Service.Exit)
