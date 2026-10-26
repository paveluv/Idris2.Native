||| Where the runtime implements a foreign function of the libraries a
||| program uses (`candidates`), and which of the prelude's functions
||| between strings and lists the string encoding's module implements
||| (`stringFunctions`).
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Native.Codegen.Linkage.Routine` says what it is).
module Native.Codegen.Linkage.ForeignFunctions

import Native.Codegen.Linkage.RuntimeModule
import Native.Codegen.Linkage.SystemLibrary

import Core.Name
import Core.Name.Namespace
import Data.SortedMap
import Native.Types.Enc as Types
import Native.Types.StringEnc as Types

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

||| One of the prelude's foreign functions between strings and lists:
||| `fastPack`, a list of characters as a string; `fastUnpack`, a string as
||| the list of its characters; and `fastConcat`, a list of strings as one.
public export
data StringFunction = FastPack | FastUnpack | FastConcat

||| The prelude's functions between strings and lists that the string
||| encoding's module implements, each by its name, with which it is and the
||| module's function of the same name that implements it: all three under
||| an encoding with a string module, none under one without.
export
stringFunctions : Types.StringEnc -> SortedMap Name (StringFunction, Name)
stringFunctions enc = case RuntimeModule.stringModule enc of
  Nothing => empty
  Just m =>
    let prelude = mkNamespace "Prelude.Types" in
    fromList
      (map (\(f, p) => (NS prelude (UN (Basic f)), (p, NS m (UN (Basic f)))))
         [("fastPack", FastPack), ("fastUnpack", FastUnpack), ("fastConcat", FastConcat)])

||| Where a foreign function may be implemented, in the order the code
||| generator looks: the string encoding's module, for the prelude's
||| functions between strings and lists (`stringFunctions`); the system
||| library's (`SystemLibrary`), for the libraries' OS surface; and the
||| support tier, for Idris's own primitives and values (pointers,
||| buffers). The first the loaded runtime defines implements it: a flat
||| function by the boundary, which converts each argument and the result
||| as their types say; an ordinary one by a call, which needs none. A
||| foreign function none implements stays `Unsupported`.
export
candidates : Types.Enc -> SystemLibrary -> Name -> List Name
candidates enc lib n =
  maybe [] (\f => [snd f]) (lookup n (stringFunctions enc.string))
    ++ [under (SystemLibrary.systemRoot lib) n, under RuntimeModule.supportRoot n]
