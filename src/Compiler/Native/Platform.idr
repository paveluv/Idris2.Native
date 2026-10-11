||| The platforms: what a program is compiled for, an architecture and an
||| operating system. The architecture decides the instructions, the
||| registers and the conventions of calls (`Compiler.Native.Target`); the
||| operating system decides how a program reaches the system, which the
||| runtime's OS services hide from the rest of it (`Compiler.Native.Linkage`),
||| and the executable's format and branding.
|||
||| How each operating system may be reached differs in kind, not only in
||| numbers. Linux and FreeBSD keep a stable system-call ABI, each with its
||| own numbers per architecture and its own error convention. OpenBSD takes
||| system calls only from libc's text, macOS's one stable ABI is libSystem,
||| and Windows has no stable system calls at all, only kernel32: on those, a
||| program calls into a system library, in the platform's C convention,
||| through the executable format's imports. Every one is named here, so that
||| a choice of platform is a value the backend matches on; the ones not built
||| yet are refused by name.
module Compiler.Native.Platform

import Data.List

%default total

||| An instruction set.
public export
data Arch = X86_64 | AArch64

||| An operating system.
public export
data OS = Linux | FreeBSD | OpenBSD | MacOS | Windows

||| What a program is compiled for.
public export
record Platform where
  constructor MkPlatform
  arch : Arch
  os : OS

public export
Eq Arch where
  X86_64 == X86_64 = True
  AArch64 == AArch64 = True
  _ == _ = False

public export
Eq OS where
  Linux == Linux = True
  FreeBSD == FreeBSD = True
  OpenBSD == OpenBSD = True
  MacOS == MacOS = True
  Windows == Windows = True
  _ == _ = False

public export
Eq Platform where
  MkPlatform a o == MkPlatform a' o' = a == a' && o == o'

||| As the directive `target=` writes them.
export
Show Arch where
  show X86_64 = "x86_64"
  show AArch64 = "aarch64"

export
Show OS where
  show Linux = "linux"
  show FreeBSD = "freebsd"
  show OpenBSD = "openbsd"
  show MacOS = "macos"
  show Windows = "windows"

export
Show Platform where
  show (MkPlatform a o) = show a ++ "-" ++ show o

||| The platform a `target=` names: `<arch>-<os>`.
export
parsePlatform : String -> Maybe Platform
parsePlatform s = case break (== '-') (unpack s) of
  (a, '-' :: o) => [| MkPlatform (arch (pack a)) (os (pack o)) |]
  _ => Nothing
  where
    arch : String -> Maybe Arch
    arch "x86_64" = Just X86_64
    arch "aarch64" = Just AArch64
    arch _ = Nothing

    os : String -> Maybe OS
    os "linux" = Just Linux
    os "freebsd" = Just FreeBSD
    os "openbsd" = Just OpenBSD
    os "macos" = Just MacOS
    os "windows" = Just Windows
    os _ = Nothing

||| The platforms built: x86-64 Linux alone.
export
built : Platform -> Bool
built (MkPlatform X86_64 Linux) = True
built _ = False

||| The platform a program is compiled for unless a directive says otherwise.
export
defaultPlatform : Platform
defaultPlatform = MkPlatform X86_64 Linux
