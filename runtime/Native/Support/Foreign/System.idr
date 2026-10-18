||| The foreign functions of `base`'s `System`, as the runtime implements
||| them: each a flat function of the foreign one's name and type, which the
||| native code generator binds it to (`foreignFunctions`), so that ordinary
||| code calls it through the boundary, which converts its arguments and its
||| result as their types say.
module Native.Support.Foreign.System

import Native.Runtime.Memory
import Native.Runtime.Ordo as Runtime
-- lint: allow import-unused: the flat check reaches through argumentCount's body, which uses raw memory
import Native.Runtime.Raw as Runtime
import Native.Runtime.System

%default total

%cg native flat Support.Foreign.System.prim__exit
||| End the process with the status: its low byte is what the parent sees.
export
prim__exit : Int -> PrimIO ()
prim__exit status w = let (Runtime.MkOrdo # ()) = Runtime.System.exit (cast status) Runtime.MkOrdo in MkIORes () w

%cg native flat Support.Foreign.System.prim__getArgCount
||| How many arguments the program has, its name the first, as the system
||| gave them.
export
prim__getArgCount : PrimIO Int
prim__getArgCount w = let (Runtime.MkOrdo # n) = Runtime.Memory.argumentCount Runtime.MkOrdo in MkIORes (cast n) w
