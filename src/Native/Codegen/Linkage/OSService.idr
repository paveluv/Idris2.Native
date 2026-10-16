||| Where a platform's OS services are (`platformModule`): the module of the
||| runtime that implements every service (`Native.Services` says what they
||| are) for the platform, by its record `services`.
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Native.Codegen.Linkage.Routine` says what it is).
module Native.Codegen.Linkage.OSService

import Native.Codegen.Linkage.RuntimeModule

import Core.Name.Namespace
import Native.Codegen.Platform

%default total

||| The module of the runtime that implements the OS services on a platform,
||| if the platform is built.
export
platformModule : Platform -> Maybe Namespace
platformModule (MkPlatform Platform.X86_64 Platform.Linux) =
  Just (RuntimeModule.runtimeModule "OS.LinuxX86_64")
platformModule _ = Nothing
