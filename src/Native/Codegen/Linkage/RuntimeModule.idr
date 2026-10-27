||| Where the runtime library's modules are: its core's under one root
||| (`runtimeModule`), its support tier's under another (`supportModule`),
||| each system library's under its own (`systemModule`), all the runtime's
||| part of the project's; and in which of them the contract's entries are
||| declared, where the code generator looks for them (`inCore`,
||| `declaresExterns`, `stringModule`, `bignumModule`).
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Native.Codegen.Linkage.Routine` says what it is).
module Native.Codegen.Linkage.RuntimeModule

import Native.Codegen.Linkage.SystemLibrary

import Core.Name.Namespace
import Data.String
import Native.HeapObj.ValEnc as HeapObj
import Native.Types.BignumEnc as Types
import Native.Types.Enc as Types
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

||| A module of a system library (`SystemLibrary`), by its name under its
||| root.
public export
systemModule : SystemLibrary -> String -> Namespace
systemModule lib = under (SystemLibrary.systemRoot lib)

||| Whether a namespace is the runtime library's, of any tier.
public export
inRuntime : Namespace -> Bool
inRuntime ns = let s =
                     show ns in any (\r => s == r || isPrefixOf (r ++ ".") s)
                       ([runtimeRoot, supportRoot]
                        ++ map SystemLibrary.systemRoot SystemLibrary.allSystemLibraries)

||| Whether a namespace is the runtime's core's: its root, or a module under
||| it. The routines are the core's functions of their ports, so the
||| contract looks for them only in its modules, and decodes no other
||| tier's definitions to find them; a function of a routine's port
||| elsewhere is an ordinary function, called as one. The root is made
||| once, with the rule, not at each namespace the rule is given: a walk of
||| the context gives it every entry's.
export
inCore : Namespace -> Bool
inCore = let root = runtimeModule "" in \ns => isParentOf root ns

||| The support tier's module that declares the externs of the string
||| routines the runtime's own code calls (`Types.StringRoutine`'s text,
||| as the system's bytes).
export
textModule : Namespace
textModule = supportModule "Text"

||| Whether a namespace is of the modules where the runtime declares its
||| externs: its core's, which declare the inline externs and the OS
||| services', and the module of the system's text (`textModule`), which
||| declares the string routines' that the runtime's own code calls. The
||| contract looks for every extern only there, each by its port, so it
||| decodes no other module's definitions to find them; and an extern of
||| the runtime anywhere else is refused as its module is built
||| (`Realised.checkExterns`), since the contract would not find it. The
||| namespaces are made once, with the rule, as `inCore`'s root is.
export
declaresExterns : Namespace -> Bool
declaresExterns = let core = inCore
                      text = textModule in
                  \ns => core ns || ns == text

||| The support tier's module that lays strings out under the encoding: the
||| one module of the runtime that reads a string's header or bytes. Every
||| other part of the runtime asks it. None yet for UTF-32.
export
stringModule : Types.StringEnc -> Maybe Namespace
stringModule Types.StringEnc.Utf8 = Just (supportModule "String.Utf8")
stringModule Types.StringEnc.Utf32 = Nothing

||| The support tier's module that lays `Integer`s outside the fixnums out
||| under the program's encodings: the one module of the runtime that reads
||| a `BIGNUM`'s limbs. One for 64-bit limbs in sign-magnitude, under a
||| value encoding with fixnums, where an integer in their range is one;
||| none yet for another limb width or sign, nor where every integer is an
||| object.
export
bignumModule : Types.Enc -> Maybe Namespace
bignumModule (Types.MkEnc HeapObj.ValEnc.NoFixnums _ _) = Nothing
bignumModule
  (Types.MkEnc _ (Types.MkBignumEnc Types.BignumEnc.Limb64 Types.BignumEnc.SignMagnitude) _) =
    Just (supportModule "Bignum.SignMagnitude")
bignumModule _ = Nothing
