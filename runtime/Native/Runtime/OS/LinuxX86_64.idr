||| The OS services on x86-64 Linux, by raw system calls. Linux keeps a
||| stable system-call ABI: the number in rax and the arguments in rdi, rsi,
||| rdx, r10, r8 and r9, the result in rax, an error as a number from -4095
||| to -1. The numbers here are x86-64's; another architecture's Linux has
||| its own. Each function is declared by its service's port
||| (`Native.Service`), which Idris checks; the native code generator finds
||| each by that type, and binds the service's extern to it when a program
||| is compiled for x86-64 Linux, loading this module for it. Nothing in the
||| generic runtime imports it.
module Native.Runtime.OS.LinuxX86_64

import Native.Runtime.OS.Syscall

import Native.Failure
import Native.HeapObj.Shape
import Native.Port
import Native.Runtime.Bits
import Native.Runtime.Memory
import Native.Runtime.Ordo
import Native.Runtime.PortTy
import Native.Runtime.Raw
import Native.Runtime.State
import Native.Service

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| Whether a system call's result is an error.
failed : Bits64 -> Bool
failed r = r > 0xFFFFFFFFFFFFF000

||| Whether a system call's result is a success; if it is an error, its
||| reason recorded as the runtime's last failure.
succeeded : Bits64 -> Ordo.Op Ordo Bool
succeeded r =
  if failed r
     then do
       State.setState State.lastFailure (failureOf (0 - r))
       Ordo.pure False
     else Ordo.pure True
  where
    ||| The reason Linux's error number names, as its code (`Native.Failure`).
    failureOf : (errno : Bits64) -> Bits64
    failureOf e =
      if e == 2 then Failure.code Failure.NotFound -- ENOENT
      else if e == 13 then Failure.code Failure.PermissionDenied -- EACCES
      else if e == 1 then Failure.code Failure.NotPermitted -- EPERM
      else if e == 17 then Failure.code Failure.Exists -- EEXIST
      else if e == 20 then Failure.code Failure.NotADirectory -- ENOTDIR
      else if e == 21 then Failure.code Failure.IsADirectory -- EISDIR
      else if e == 39 then Failure.code Failure.NotEmpty -- ENOTEMPTY
      else if e == 16 then Failure.code Failure.Busy -- EBUSY
      else if e == 24 || e == 23 then Failure.code Failure.TooManyOpen -- EMFILE, ENFILE
      else if e == 28 then Failure.code Failure.NoSpace -- ENOSPC
      else if e == 30 then Failure.code Failure.ReadOnly -- EROFS
      else if e == 36 then Failure.code Failure.NameTooLong -- ENAMETOOLONG
      else if e == 40 then Failure.code Failure.LinkLoop -- ELOOP
      else if e == 9 then Failure.code Failure.BadHandle -- EBADF
      else if e == 22 then Failure.code Failure.Invalid -- EINVAL
      else if e == 4 then Failure.code Failure.Interrupted -- EINTR
      else if e == 11 then Failure.code Failure.WouldBlock -- EAGAIN
      else if e == 32 then Failure.code Failure.BrokenPipe -- EPIPE
      else if e == 5 then Failure.code Failure.InputOutput -- EIO
      else if e == 12 then Failure.code Failure.NoMemory -- ENOMEM
      else if e == 18 then Failure.code Failure.CrossDevice -- EXDEV
      else Failure.code Failure.Other

%cg native flat Runtime.OS.LinuxX86_64.exit
export
exit : PortTy Memory.Addr (Service.port Service.Exit)
exit status = do
  -- exit_group(status)
  _ <- Syscall.syscall 231 status 0 0 0 0 0
  Ordo.pure ()

%cg native flat Runtime.OS.LinuxX86_64.write
export
write : PortTy Memory.Addr (Service.port Service.Write)
write handle address bytes = do
  -- write(handle, address, bytes)
  r <- Syscall.syscall 1 handle (Raw.rawWord address) bytes 0 0 0
  ok <- succeeded r
  Ordo.pure (if ok then r else 0)

%cg native flat Runtime.OS.LinuxX86_64.reserve
export
reserve : PortTy Memory.Addr (Service.port Service.Reserve)
reserve bytes = do
  -- mmap(NULL, bytes, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0):
  -- no overcommit setting counts a range that is not readable
  r <- Syscall.syscall 9 0 bytes 0 0x4022 0xFFFFFFFFFFFFFFFF 0
  ok <- succeeded r
  -- the system gives the range's address as a word
  Ordo.pure (Raw.fromWord (if ok then r else 0))

%cg native flat Runtime.OS.LinuxX86_64.commit
export
commit : PortTy Memory.Addr (Service.port Service.Commit)
commit address bytes = do
  -- mprotect(address, bytes, PROT_READ | PROT_WRITE): the pages are zero when first touched
  r <- Syscall.syscall 10 (Raw.rawWord address) bytes 3 0 0 0
  ok <- succeeded r
  Ordo.pure (if ok then 1 else 0)

%cg native flat Runtime.OS.LinuxX86_64.release
export
release : PortTy Memory.Addr (Service.port Service.Release)
release address bytes = do
  -- madvise(address, bytes, MADV_DONTNEED), then mprotect(address, bytes, PROT_NONE)
  _ <- Syscall.syscall 28 (Raw.rawWord address) bytes 4 0 0 0
  _ <- Syscall.syscall 10 (Raw.rawWord address) bytes 0 0 0 0
  Ordo.pure ()

%cg native flat Runtime.OS.LinuxX86_64.pageBytes
export
pageBytes : PortTy Memory.Addr (Service.port Service.PageBytes)
pageBytes = Ordo.pure 4096

%cg native flat Runtime.OS.LinuxX86_64.stackLimit
export
stackLimit : PortTy Memory.Addr (Service.port Service.StackLimit)
stackLimit = do
  -- getrlimit(RLIMIT_STACK, buffer): the soft limit in the buffer's first word,
  -- left 0 if the call fails
  buffer <- State.scratchArea
  Memory.storeAt buffer 0 0
  _ <- Syscall.syscall 97 3 (Raw.rawWord buffer) 0 0 0 0
  Memory.loadAt buffer 0

%cg native flat Runtime.OS.LinuxX86_64.prepareTerminal
export
prepareTerminal : PortTy Memory.Addr (Service.port Service.PrepareTerminal)
prepareTerminal = Ordo.pure () -- a Linux terminal takes escape sequences as it is

||| The first word of the size of the terminal the standard input is, or else
||| the standard output, its lines in the low 16 bits and its columns in the
||| next 16; 0 if neither is a terminal. The kernel writes it into the
||| state's scratch bytes.
terminalSize : Ordo.Op Ordo Bits64
terminalSize = do
  -- ioctl(handle, TIOCGWINSZ, buffer): struct winsize, its rows and its
  -- columns the first two of four 16-bit fields
  buffer <- State.scratchArea
  Memory.storeAt buffer 0 0
  r <- Syscall.syscall 16 0 0x5413 (Raw.rawWord buffer) 0 0 0
  r' <- if failed r then Syscall.syscall 16 1 0x5413 (Raw.rawWord buffer) 0 0 0 else Ordo.pure r
  if failed r' then Ordo.pure 0 else Memory.loadAt buffer 0

%cg native flat Runtime.OS.LinuxX86_64.terminalColumns
export
terminalColumns : PortTy Memory.Addr (Service.port Service.TerminalColumns)
terminalColumns = do
  size <- terminalSize
  Ordo.pure (Bits.shiftR size 16 .&. 0xFFFF)

%cg native flat Runtime.OS.LinuxX86_64.terminalLines
export
terminalLines : PortTy Memory.Addr (Service.port Service.TerminalLines)
terminalLines = do
  size <- terminalSize
  Ordo.pure (size .&. 0xFFFF)

%cg native flat Runtime.OS.LinuxX86_64.changeDirectory
export
changeDirectory : PortTy Memory.Addr (Service.port Service.ChangeDirectory)
changeDirectory path = do
  -- chdir(path)
  r <- Syscall.syscall 80 (Raw.rawWord path) 0 0 0 0 0
  ok <- succeeded r
  Ordo.pure (if ok then 1 else 0)

%cg native flat Runtime.OS.LinuxX86_64.currentDirectory
export
currentDirectory : PortTy Memory.Addr (Service.port Service.CurrentDirectory)
currentDirectory address bytes = do
  -- getcwd(address, bytes): the path's length with its zero byte
  r <- Syscall.syscall 79 (Raw.rawWord address) bytes 0 0 0 0
  ok <- succeeded r
  Ordo.pure (if ok then 1 else 0)

%cg native flat Runtime.OS.LinuxX86_64.createDirectory
export
createDirectory : PortTy Memory.Addr (Service.port Service.CreateDirectory)
createDirectory path = do
  -- mkdir(path, 0777), which the process's umask narrows
  r <- Syscall.syscall 83 (Raw.rawWord path) 0x1FF 0 0 0 0
  ok <- succeeded r
  Ordo.pure (if ok then 1 else 0)

%cg native flat Runtime.OS.LinuxX86_64.removeDirectory
export
removeDirectory : PortTy Memory.Addr (Service.port Service.RemoveDirectory)
removeDirectory path = do
  -- rmdir(path)
  r <- Syscall.syscall 84 (Raw.rawWord path) 0 0 0 0 0
  ok <- succeeded r
  Ordo.pure (if ok then 1 else 0)
