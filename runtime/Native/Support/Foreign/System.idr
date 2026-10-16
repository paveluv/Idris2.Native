||| The foreign functions of `base`'s `System`, as the runtime implements
||| them: each a flat function of the foreign one's name and type, which the
||| native code generator binds it to (`foreignFunctions`), so that ordinary
||| code calls it through the boundary, which converts its arguments and its
||| result as their types say.
module Native.Support.Foreign.System

import Native.Runtime.Heap as Runtime
import Native.Runtime.System

%default total

%cg native flat Support.Foreign.System.prim__exit
||| End the process with the status: its low byte is what the parent sees.
export
prim__exit : Int -> PrimIO ()
prim__exit status w = let (Runtime.MkHeap # ()) = Runtime.System.exit (cast status) Runtime.MkHeap in MkIORes () w
