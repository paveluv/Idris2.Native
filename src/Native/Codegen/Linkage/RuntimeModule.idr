||| Where the runtime library's modules are (`runtimeModule`): under one
||| root, the runtime's part of the project's.
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Native.Codegen.Linkage.Routine` says what it is).
module Native.Codegen.Linkage.RuntimeModule

import Core.Name.Namespace
import Data.String
import Native.Types.StringEnc as Types

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

||| The runtime's module that lays strings out under the encoding: the one
||| module of the runtime that reads a string's header or bytes. Every other
||| part of the runtime asks it. None yet for UTF-32.
export
stringModule : Types.StringEnc -> Maybe Namespace
stringModule Types.StringEnc.Utf8 = Just (runtimeModule "String.Utf8")
stringModule Types.StringEnc.Utf32 = Nothing
