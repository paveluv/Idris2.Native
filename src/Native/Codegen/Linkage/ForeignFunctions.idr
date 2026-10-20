||| Where the runtime implements a foreign function of the libraries a
||| program uses (`candidates`).
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Native.Codegen.Linkage.Routine` says what it is).
module Native.Codegen.Linkage.ForeignFunctions

import Native.Codegen.Linkage.RuntimeModule
import Native.Codegen.Linkage.SystemLibrary

import Core.Name
import Core.Name.Namespace
import Native.Types.Enc as Types

%default total

||| The definition that would implement a foreign function under a root: of
||| the foreign one's module path and name, under the root's `Foreign`
||| (`System.prim__exit` by `Native.System.Foreign.System.prim__exit` under
||| the system tier's root). A foreign function is bound by its Idris name,
||| whatever names the library gives it for C or Scheme.
export
under : (root : String) -> Name -> Name
under root (NS ns f) = NS (mkNamespace (root ++ ".Foreign." ++ show ns)) f
under root n = NS (mkNamespace (root ++ ".Foreign")) n

||| Where a foreign function may be implemented, in the order the code
||| generator looks: the string encoding's module, for the primitives of
||| lists of characters and strings; the system library's (`SystemLibrary`),
||| for the libraries' OS surface; and the support tier, for Idris's own
||| primitives and values (pointers, buffers). The first the loaded runtime
||| defines implements it: a flat function by the boundary, which converts
||| each argument and the result as their types say; an ordinary one by a
||| call, which needs none. A foreign function none implements stays
||| `Unsupported`.
export
candidates : Types.Enc -> SystemLibrary -> Name -> List Name
candidates enc lib n =
  strings ++ [under (SystemLibrary.systemRoot lib) n, under RuntimeModule.supportRoot n]
  where
    -- the string module's functions of the prelude's string primitives
    strings : List Name
    strings = case (n, RuntimeModule.stringModule enc.string) of
      (NS ns (UN (Basic f)), Just m) =>
        if ns == mkNamespace "Prelude.Types" && elem f ["fastPack", "fastUnpack", "fastConcat"]
          then [NS m (UN (Basic f))] else []
      _ => []
