||| The runtime of Idris 2's native code generator: the routines generated
||| code reaches, written in Idris, as flat functions. A program does not
||| import it; the code generator loads it, by this module, which imports
||| the others.
module Runtime

import public Runtime.Heap
import public Runtime.Memory
import public Runtime.Start
import public Runtime.System
