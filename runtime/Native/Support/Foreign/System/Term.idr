||| The foreign functions of `base`'s `System.Term`, as the runtime implements
||| them: the terminal made ready and its size, through the OS services, each
||| a flat function of the foreign one's name and type
||| (`Native.Support.Foreign.System` says how they are bound).
module Native.Support.Foreign.System.Term

import Native.Runtime.Ordo as Runtime
import Native.Runtime.OS

%default total

%cg native flat Support.Foreign.System.Term.prim__setupTerm
||| Make the terminal of the output take escape sequences, where the system
||| has to be asked.
export
prim__setupTerm : PrimIO ()
prim__setupTerm w = let (Runtime.MkOrdo # ()) =
                          Runtime.OS.osPrepareTerminal Runtime.MkOrdo in MkIORes () w

%cg native flat Support.Foreign.System.Term.prim__getTermCols
||| The columns of the terminal the standard input is, or else the standard
||| output; 0 if neither is a terminal.
export
prim__getTermCols : PrimIO Int
prim__getTermCols w = let (Runtime.MkOrdo # n) =
                            Runtime.OS.osTerminalColumns Runtime.MkOrdo in MkIORes (cast n) w

%cg native flat Support.Foreign.System.Term.prim__getTermLines
||| The lines of the terminal the standard input is, or else the standard
||| output; 0 if neither is a terminal.
export
prim__getTermLines : PrimIO Int
prim__getTermLines w = let (Runtime.MkOrdo # n) =
                             Runtime.OS.osTerminalLines Runtime.MkOrdo in MkIORes (cast n) w
