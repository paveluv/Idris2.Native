||| The system libraries (`SystemLibrary`): what implements the libraries'
||| OS surface for a program (files, directories, the environment, errors,
||| memory outside the heap, the clocks, the terminal), the part of `base`
||| that C programs have from libc. One is chosen for each program, by the
||| platform or a directive, and the code generator binds each foreign
||| function the program reaches to its implementation in it
||| (`ForeignFunctions.candidates`), whatever the others implement.
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Native.Codegen.Linkage.Routine` says what it is).
module Native.Codegen.Linkage.SystemLibrary

%default total

||| The system libraries.
public export
data SystemLibrary
  = ||| The runtime's system tier: ordinary Idris over the core's OS
    ||| services and the support tier (`Native.System`). On a system whose
    ||| services are system calls, nothing below it is C.
    NativeSystem

||| As the directive `system=` writes it.
export
Show SystemLibrary where
  show NativeSystem = "native"

||| The system library a `system=` names.
export
parseSystemLibrary : String -> Maybe SystemLibrary
parseSystemLibrary "native" = Just NativeSystem
parseSystemLibrary _ = Nothing

||| Every system library, once.
export
allSystemLibraries : List SystemLibrary
allSystemLibraries = [NativeSystem]

||| The root of a system library's modules, the runtime's.
public export
systemRoot : SystemLibrary -> String
systemRoot NativeSystem = "Native.System"
