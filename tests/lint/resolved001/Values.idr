||| A module outside the runtime's core that converts a value through the
||| core's conversion, which takes a value of any type for what its caller
||| says: reported (`sealed-values`), as only the support tier's door
||| (`Native.Support.Obj`) may, with the representation contract's evidence.
module Values

import Native.Flat.Uniform
import Native.HeapObj.Shape
import Native.Runtime.Memory
import Native.Runtime.Ordo

%default total

export
asString : Addr VALUES -> Op Ordo (Uniform String)
asString a = Memory.objectValue a
