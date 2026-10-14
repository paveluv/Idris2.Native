||| Where a function may convert between words and addresses (`convertsIn`).
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Compiler.Native.Linkage.Routine` says what it is).
module Compiler.Native.Linkage.ConvertsIn

import Core.Name

%default total

||| Whether a function may convert between words and addresses in the term
||| IR: only the functions of the module that implements the runtime's
||| memory, where an address is made from a word and taken apart.
public export
convertsIn : Name -> Bool
convertsIn (NS ns _) = ns == mkNamespace "Runtime.Memory"
convertsIn _ = False
