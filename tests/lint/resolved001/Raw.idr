||| A module that reaches memory by a raw extern of the contract, not
||| through the runtime's memory module, which wraps it: reported
||| (`extern-owner`).
module Raw

import Native.Heap
import Native.Intrinsics

%default total

export
raw : Bits64 -> Op Heap Bits64
raw a = prim__load64 a 0
