||| The foreign functions of `base`'s `System.File.Process`, as the system
||| tier implements them: each an ordinary function of the foreign one's
||| name and type (`Native.System` says how they are bound).
module Native.System.Foreign.System.File.Process

%default total

||| `fflush`: 0, as a file's writes are not buffered, so nothing waits to
||| be flushed.
export
prim__flush : AnyPtr -> PrimIO Int
prim__flush _ w = MkIORes 0 w
