||| Where the runtime library's modules are: its core's under one root
||| (`runtimeModule`), its support tier's under another (`supportModule`),
||| both the runtime's part of the project's.
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Native.Codegen.Linkage.Routine` says what it is).
module Native.Codegen.Linkage.RuntimeModule

import Core.Name.Namespace
import Data.String
import Native.Types.BignumEnc as Types
import Native.Types.StringEnc as Types

%default total

||| The root of the runtime's core: the heap, the calling convention and
||| the OS services.
public export
runtimeRoot : String
runtimeRoot = "Native.Runtime"

||| The root of the runtime's support tier: the primitive types and the
||| foreign functions of the libraries Idris ships.
public export
supportRoot : String
supportRoot = "Native.Support"

||| A module by its name under a root (`"Memory"` under `Native.Runtime`
||| for `Native.Runtime.Memory`); the root itself by `""`.
under : (root : String) -> String -> Namespace
under root "" = mkNamespace root
under root m = mkNamespace (root ++ "." ++ m)

||| A module of the runtime library, by its name under the root (`"Memory"`
||| for `Native.Runtime.Memory`); the root itself, the module that imports
||| the generic ones, by `""`.
public export
runtimeModule : String -> Namespace
runtimeModule = under runtimeRoot

||| A module of the support tier, by its name under its root, as
||| `runtimeModule` names the core's.
public export
supportModule : String -> Namespace
supportModule = under supportRoot

||| Whether a namespace is the runtime library's, of either tier.
public export
inRuntime : Namespace -> Bool
inRuntime ns = let s =
                     show ns in any (\r => s == r || isPrefixOf (r ++ ".") s)
                       [runtimeRoot, supportRoot]

||| The support tier's module that lays strings out under the encoding: the
||| one module of the runtime that reads a string's header or bytes. Every
||| other part of the runtime asks it. None yet for UTF-32.
export
stringModule : Types.StringEnc -> Maybe Namespace
stringModule Types.StringEnc.Utf8 = Just (supportModule "String.Utf8")
stringModule Types.StringEnc.Utf32 = Nothing

||| The support tier's module that lays `Integer`s outside the fixnums out
||| under the bignum encoding: none yet, for any encoding.
export
bignumModule : Types.BignumEnc -> Maybe Namespace
bignumModule _ = Nothing
