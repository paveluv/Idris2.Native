||| The runtime of Idris 2's native code generator: the routines generated
||| code reaches, written in Idris, as flat functions. A program does not
||| import it; the code generator loads it, by this module, which imports
||| the others.
|||
||| The runtime holds what Idris itself treats as runtime, and nothing else:
||| its primitive types and their operations; the values of the compiled
||| language (constructors, partial applications, continuations); the calling
||| convention (start-up, `apply`, the program's end, crash); the heap, which
||| finalizers and `GCPtr` assume; the process; and the foreign functions of
||| the libraries Idris ships (`prelude`, `base`, `contrib`, `network`).
||| A type Idris does not define, or an operation its libraries do not
||| declare foreign, is not the runtime's: a faster map, a matrix, a rope
||| are libraries of their own.
|||
||| It is in two tiers. This one, the core, is the heap (its spaces,
||| allocation, the collector, rooting), the calling convention and the OS
||| services, and knows objects by their shapes alone (`Native.HeapObj.Shape`),
||| never their types; it imports the contract and nothing of the type
||| layer, which the linter's layers hold. It changes rarely, and by
||| decision: a new shape, or a new space (`Native.Runtime.Space`). The
||| support tier (`Native.Support`) implements the types over it.
module Native.Runtime

import public Native.Runtime.Bits
import public Native.Runtime.Collect
import public Native.Runtime.Heap
import public Native.Runtime.Memory
import public Native.Runtime.OS
import public Native.Runtime.Space
import public Native.Runtime.Start
import public Native.Runtime.State
import public Native.Runtime.System

%default total
