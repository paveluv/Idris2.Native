||| The foreign functions of `base`'s `System.File.Virtual`, as the system
||| tier implements them: the standard files, slots 0, 1 and 2 of the table
||| of open files (`Native.System.File`), each an ordinary function of the
||| foreign one's name and type (`Native.System` says how they are bound).
module Native.System.Foreign.System.File.Virtual

import Native.System.File

%default total

export
prim__stdin, prim__stdout, prim__stderr : AnyPtr
prim__stdin = File.standard 0
prim__stdout = File.standard 1
prim__stderr = File.standard 2
