||| The OS services (`OSService`): what an operating system provides to the
||| rest of the runtime.
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Compiler.Native.Linkage.Routine` says what it is).
module Compiler.Native.Linkage.OSService

import Compiler.Native.HeapObject.Enc
import Compiler.Native.IRCommon.Ty
import Compiler.Native.Platform
import Core.Name

%default total

||| An OS service: what the runtime asks of the operating system, by the
||| name of the generic runtime's `%extern` for it, `Runtime.OS.prim__os_`
||| and the service's own name, with the registers of its arguments, the
||| token among them taking none, and of its result. A platform's module
||| implements it as a function of the service's own name.
public export
record OSService (0 enc : Enc) where
  constructor MkOSService
  service : String
  params : List (Ty enc)
  results : List (Ty enc)

||| The OS services. A result that reports success is 1 for success and 0
||| for failure, so that the generic runtime decides what a failure means.
|||
||| * `exit status`: end the process.
||| * `write handle address bytes`: write the bytes to the standard handle
|||   (1 the output, 2 the errors); the bytes written.
||| * `reserve bytes`: reserve address space, readable by nothing, which no
|||   memory is committed to; its address, 0 if there is none.
||| * `commit address bytes`: make reserved whole pages readable and
|||   writable, and zero; success.
||| * `release address bytes`: give committed whole pages back and reserve
|||   them again.
||| * `stackLimit`: the most bytes the process's stack may grow to, 0 if the
|||   system does not say.
||| * `pageBytes`: the system's page, the bytes memory is committed and
|||   released by.
export
osServices : {0 enc : Enc} -> List (OSService enc)
osServices =
  [ MkOSService "exit" [W64] []
  , MkOSService "write" [W64, W64, W64] [W64]
  , MkOSService "reserve" [W64] [W64]
  , MkOSService "commit" [W64, W64] [W64]
  , MkOSService "release" [W64, W64] []
  , MkOSService "stackLimit" [] [W64]
  , MkOSService "pageBytes" [] [W64] ]

||| The generic runtime's `%extern` for a service.
export
serviceExtern : OSService enc -> Name
serviceExtern s = NS (mkNamespace "Runtime.OS") (UN (Basic ("prim__os_" ++ s.service)))

||| The module of the runtime that implements the OS services on a platform,
||| if the platform is built.
export
platformModule : Platform -> Maybe Namespace
platformModule (MkPlatform X86_64 Linux) = Just (mkNamespace "Runtime.OS.LinuxX86_64")
platformModule _ = Nothing

||| The function that implements a service on the platform.
export
serviceFunction : Platform -> OSService enc -> Maybe Name
serviceFunction p s = (\ns => NS ns (UN (Basic s.service))) <$> platformModule p

||| Each service's extern bound to its function on the platform.
export
serviceBindings : {0 enc : Enc} -> Platform -> List (Name, Name)
serviceBindings p = mapMaybe (\s => (serviceExtern s,) <$> serviceFunction p s) (osServices {enc})
