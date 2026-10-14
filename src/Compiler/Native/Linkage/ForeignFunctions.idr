||| The foreign functions a program's libraries use that the runtime
||| implements (`foreignFunctions`).
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Compiler.Native.Linkage.Routine` says what it is).
module Compiler.Native.Linkage.ForeignFunctions

import Compiler.Native.HeapObject.Enc
import Compiler.Native.Linkage.Routine
import Core.Name
import Core.Name.Namespace

%default total

||| The foreign functions of the libraries a program uses, `prelude` and
||| `base`, that the runtime implements, each with the flat function that
||| does: of the same type position by position, so that the lowering gives
||| the foreign function the boundary to it, which converts each argument and
||| the result as their types say. Most are `Runtime.Foreign`'s, by the
||| foreign one's module path and name (`System.prim__exit` by
||| `Runtime.Foreign.System.prim__exit`); those that lay strings out are the
||| string module's, under the program's encoding. A foreign function is
||| bound by its Idris name, whatever names the library gives it for C or
||| Scheme; one not listed stays `Unsupported`.
export
foreignFunctions : Enc -> List (Name, Name)
foreignFunctions enc =
  [ mirrored (NS (mkNamespace "System") (UN (Basic "prim__exit"))) ]
  ++ maybe [] (\ns => map (\f => (NS (mkNamespace "Prelude.Types") (UN (Basic f)), NS ns (UN (Basic f))))
                          ["fastPack", "fastUnpack", "fastConcat"])
           (stringModule enc.string)
  where
    mirrored : Name -> (Name, Name)
    mirrored n@(NS ns f) = (n, NS (mkNamespace ("Runtime.Foreign." ++ show ns)) f)
    mirrored n = (n, NS (mkNamespace "Runtime.Foreign") n)
