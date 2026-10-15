||| Where a function may convert between words and addresses (`convertsIn`).
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Native.Codegen.Linkage.Routine` says what it is).
module Native.Codegen.Linkage.ConvertsIn

import Native.Codegen.Linkage.RuntimeModule

import Core.Name
import Core.Name.Namespace

%default total

||| Whether a function may convert between words and addresses in the term
||| IR: only the functions of the module that implements the runtime's
||| memory, where an address is made from a word and taken apart.
public export
convertsIn : Name -> Bool
convertsIn (NS ns _) = ns == RuntimeModule.runtimeModule "Memory"
convertsIn _ = False
