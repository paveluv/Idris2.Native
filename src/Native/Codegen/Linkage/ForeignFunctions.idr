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
||| `Support.Foreign.System.prim__exit`), a string reached through the
||| string encoding's externs (`Support.Text`); the primitives of lists of
||| characters and strings are the string module's, under the program's
||| encoding. A foreign function is
||| bound by its Idris name, whatever names the library gives it for C or
||| Scheme; one not listed stays `Unsupported`.
export
foreignFunctions : Types.Enc -> List (Name, Name)
foreignFunctions enc =
  [ mirrored (NS (mkNamespace "System") (UN (Basic "prim__exit")))
  , mirrored (NS (mkNamespace "System") (UN (Basic "prim__getArgCount")))
  , mirrored (NS (mkNamespace "Prelude.IO") (UN (Basic "prim__putChar")))
  , mirrored (NS (mkNamespace "PrimIO") (UN (Basic "prim__nullAnyPtr")))
  , mirrored (NS (mkNamespace "System.FFI") (UN (Basic "prim__malloc")))
  , mirrored (NS (mkNamespace "System.FFI") (UN (Basic "prim__free")))
  , mirrored (NS (mkNamespace "Prelude.IO") (UN (Basic "prim__putStr")))
  , mirrored (NS (mkNamespace "Prelude.IO") (UN (Basic "prim__getString")))
  , mirrored (NS (mkNamespace "System") (UN (Basic "prim__getArg")))
  , mirrored (NS (mkNamespace "System") (UN (Basic "prim__getEnv")))
  , mirrored (NS (mkNamespace "System") (UN (Basic "prim__getEnvPair")))
  , mirrored (NS (mkNamespace "System") (UN (Basic "prim__setEnv")))
  , mirrored (NS (mkNamespace "System") (UN (Basic "prim__unsetEnv")))
  , mirrored (NS (mkNamespace "System.Directory") (UN (Basic "prim__changeDir")))
  , mirrored (NS (mkNamespace "System.Directory") (UN (Basic "prim__createDir")))
  , mirrored (NS (mkNamespace "System.Directory") (UN (Basic "prim__removeDir")))
  , mirrored (NS (mkNamespace "System.Directory") (UN (Basic "prim__currentDir")))
  , mirrored (NS (mkNamespace "System.Errno") (UN (Basic "prim__getErrno")))
  , mirrored (NS (mkNamespace "System.File.Error") (UN (Basic "prim__fileErrno")))
  , mirrored (NS (mkNamespace "System.Term") (UN (Basic "prim__setupTerm")))
  , mirrored (NS (mkNamespace "System.Term") (UN (Basic "prim__getTermCols")))
  , mirrored (NS (mkNamespace "System.Term") (UN (Basic "prim__getTermLines"))) ]
  ++ maybe [] (\ns => [ (NS (mkNamespace m) (UN (Basic f)), NS ns (UN (Basic f)))
                      | (m, f) <- [ ("Prelude.Types", "fastPack"), ("Prelude.Types", "fastUnpack")
                                  , ("Prelude.Types", "fastConcat") ] ])
           (RuntimeModule.stringModule enc.string)
  where
    mirrored : Name -> (Name, Name)
    mirrored n@(NS ns f) = (n, NS (RuntimeModule.supportModule ("Foreign." ++ show ns)) f)
    mirrored n = (n, NS (RuntimeModule.supportModule "Foreign") n)
