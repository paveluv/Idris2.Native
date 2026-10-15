||| The foreign functions of `base`'s `System`, as the runtime implements
||| them: each a flat function of the foreign one's name and type, which the
||| native code generator binds it to (`foreignFunctions`), so that ordinary
||| code calls it through the boundary, which converts its arguments and its
||| result as their types say.
module Native.Runtime.Foreign.System

import Native.Runtime.Heap
import Native.Runtime.System

%default total

%cg native flat Runtime.Foreign.System.prim__exit
||| End the process with the status: its low byte is what the parent sees.
export
prim__exit : Int -> PrimIO ()
prim__exit status w = let (Heap.MkHeap # ()) = System.exit (cast status) Heap.MkHeap in MkIORes () w
