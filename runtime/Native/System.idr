||| The runtime's own system library: what implements the libraries' OS
||| surface (files, directories, the environment, errors, `malloc`, the
||| terminal, the standard output, the clocks), the part of `base` C
||| programs have from libc, over the core's OS services and the support
||| tier. It plays libc's part only as far as `base` needs, and is one
||| system library among those the code generator may be given
||| (`Codegen.Linkage.SystemLibrary`): on a platform whose services are
||| system calls, nothing below it is C; on one that takes them only from
||| its libc, another library binds `base` to it, and this one is not
||| loaded. Idris needs none of it to run a program: a program that uses no
||| file reaches none of it.
|||
||| Each of its foreign functions is the function of the foreign one's
||| name and type under `Native.System.Foreign`, by the foreign one's
||| module path (`System.prim__exit` by
||| `Native.System.Foreign.System.prim__exit`), which the code generator
||| binds it to: a flat one through the boundary, an ordinary one by a call,
||| compiled with the program, those the program reaches. Its data are
||| values of ordinary types, kept where ordinary code keeps values. A
||| program does not import it; the code generator loads it, by this
||| module, which imports the others.
module Native.System

import public Native.System.Foreign.Prelude.IO
import public Native.System.Foreign.System
import public Native.System.Foreign.System.Directory
import public Native.System.Foreign.System.Errno
import public Native.System.Foreign.System.FFI
import public Native.System.Foreign.System.File.Buffer
import public Native.System.Foreign.System.File.Error
import public Native.System.Foreign.System.File.Handle
import public Native.System.Foreign.System.File.Meta
import public Native.System.Foreign.System.File.Process
import public Native.System.Foreign.System.File.ReadWrite
import public Native.System.Foreign.System.File.Virtual
import public Native.System.Foreign.System.Term

%default total
