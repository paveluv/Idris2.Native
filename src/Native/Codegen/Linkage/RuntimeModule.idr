||| Where the runtime library's modules are (`runtimeModule`): under one
||| root, the runtime's part of the project's.
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Native.Codegen.Linkage.Routine` says what it is).
module Native.Codegen.Linkage.RuntimeModule

import Core.Name.Namespace
import Data.String

%default total

||| The root of the runtime library's modules.
public export
runtimeRoot : String
runtimeRoot = "Native.Runtime"

||| A module of the runtime library, by its name under the root (`"Memory"`
||| for `Native.Runtime.Memory`); the root itself, the module that imports
||| the generic ones, by `""`.
public export
runtimeModule : String -> Namespace
runtimeModule "" = mkNamespace runtimeRoot
runtimeModule m = mkNamespace (runtimeRoot ++ "." ++ m)

||| Whether a namespace is the runtime library's.
public export
inRuntime : Namespace -> Bool
inRuntime ns = let s = show ns in s == runtimeRoot || isPrefixOf (runtimeRoot ++ ".") s
