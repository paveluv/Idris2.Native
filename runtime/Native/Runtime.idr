||| The runtime of Idris 2's native code generator: the routines generated
||| code reaches, written in Idris, as flat functions. A program does not
||| import it; the code generator loads it, by this module, which imports
||| the others.
module Native.Runtime

import public Native.Runtime.Bits
import public Native.Runtime.Collect
import public Native.Runtime.Heap
import public Native.Runtime.Memory
import public Native.Runtime.OS
import public Native.Runtime.Routines
import public Native.Runtime.Space
import public Native.Runtime.Start
import public Native.Runtime.State
import public Native.Runtime.System

%default total
