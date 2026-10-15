||| The routines of the generic runtime that generated code calls
||| (`routines`), as the record of the contract's `Native.Routines`: each
||| field the runtime's function for it, checked against the field's port
||| where the runtime is built. The code generator reads this record, field
||| by field, for the function that implements each routine.
module Native.Runtime.Routines

import Native.Runtime.Memory
import Native.Runtime.Space
import Native.Runtime.Start
import Native.Runtime.System

-- lint: allow import-unused: the ports unfold to `Op Heap`, which Idris
-- compares with the routines' types only where `Native.Heap` is imported
import Native.Heap
import Native.HeapObj.Kind as HeapObj
import Native.Port
import Native.Routines

%default total

||| The routines generated code calls, each checked against its port: the
||| record the code generator reads for the function that implements each.
export covering
routines : Routines (Port.PortTy (\k => Memory.Addr k))
routines =
  Routines.MkRoutines
    { start = Start.start, allocSlow = Space.allocSlow, allocMutable = Space.allocMutable
    , crash = System.crash }
