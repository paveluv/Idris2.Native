||| The foreign functions a program's libraries use that the runtime
||| implements (`foreignFunctions`).
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Native.Codegen.Linkage.Routine` says what it is).
module Native.Codegen.Linkage.ForeignFunctions

import Native.Codegen.Linkage.RuntimeModule

import Core.Name
import Core.Name.Namespace
import Native.Types.Enc as Types

%default total

||| The foreign functions of the libraries a program uses, `prelude` and
||| `base`, that the runtime implements, each with the flat function that
||| does: of the same type position by position, so that the lowering gives
||| the foreign function the boundary to it, which converts each argument and
||| the result as their types say. Most are `Support.Foreign`'s, by the
||| foreign one's module path and name (`System.prim__exit` by
||| `Support.Foreign.System.prim__exit`); those that lay strings out are the
||| string module's, under the program's encoding. A foreign function is
||| bound by its Idris name, whatever names the library gives it for C or
||| Scheme; one not listed stays `Unsupported`.
export
foreignFunctions : Types.Enc -> List (Name, Name)
foreignFunctions enc =
  [ mirrored (NS (mkNamespace "System") (UN (Basic "prim__exit")))
  , mirrored (NS (mkNamespace "System") (UN (Basic "prim__getArgCount")))
  , mirrored (NS (mkNamespace "Prelude.IO") (UN (Basic "prim__putChar")))
  , mirrored (NS (mkNamespace "PrimIO") (UN (Basic "prim__nullAnyPtr"))) ]
  ++ maybe [] (\ns => [ (NS (mkNamespace m) (UN (Basic f)), NS ns (UN (Basic f)))
                      | (m, f) <- [ ("Prelude.Types", "fastPack"), ("Prelude.Types", "fastUnpack")
                                  , ("Prelude.Types", "fastConcat"), ("Prelude.IO", "prim__putStr")
                                  , ("System", "prim__getArg"), ("System", "prim__getEnv")
                                  , ("Prelude.IO", "prim__getString") ] ])
           (RuntimeModule.stringModule enc.string)
  where
    mirrored : Name -> (Name, Name)
    mirrored n@(NS ns f) = (n, NS (RuntimeModule.supportModule ("Foreign." ++ show ns)) f)
    mirrored n = (n, NS (RuntimeModule.supportModule "Foreign") n)
