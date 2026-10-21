||| The OS services on x86-64 Linux, by direct system calls. Linux keeps a
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

import Native.Carrier
import Native.Failure
import Native.OpenFlag
import Native.Runtime.Alloc.Block as Alloc
import Native.Runtime.Bits
import Native.Runtime.ByteAddr
import Native.Runtime.Memory
import Native.Runtime.Ordo
import Native.Runtime.PortTy
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
       State.setState State.lastFailure (errnoFailure (0 - r))
       Ordo.pure False
     else Ordo.pure True
  where
    ||| The reason Linux's error number names, as its code (`Native.Failure`).
    errnoFailure : (errno : Bits64) -> Bits64
    errnoFailure e =
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
exit : PortTy (Service.port Service.Exit)
exit status = do
  -- exit_group(status)
  _ <- Syscall.syscall 231 status 0 0 0 0 0
  Ordo.pure ()

%cg native flat Runtime.OS.LinuxX86_64.write
export
write : PortTy (Service.port Service.Write)
write handle address bytes = do
  -- write(handle, address, bytes)
  r <- Syscall.syscall 1 handle (ByteAddr.toWord address) bytes 0 0 0
  ok <- succeeded r
  Ordo.pure (if ok then r else 0)

%cg native flat Runtime.OS.LinuxX86_64.reserve
export
reserve : PortTy (Service.port Service.Reserve)
reserve bytes = do
  -- mmap(NULL, bytes, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0):
  -- no overcommit setting counts a range that is not readable
  r <- Syscall.syscall 9 0 bytes 0 0x4022 0xFFFFFFFFFFFFFFFF 0
  ok <- succeeded r
  -- the system gives the range's address as a word
  Ordo.pure (ByteAddr.fromWord (if ok then r else 0))

%cg native flat Runtime.OS.LinuxX86_64.commit
export
commit : PortTy (Service.port Service.Commit)
commit address bytes = do
  -- mprotect(address, bytes, PROT_READ | PROT_WRITE): the pages are zero when first touched
  r <- Syscall.syscall 10 (ByteAddr.toWord address) bytes 3 0 0 0
  ok <- succeeded r
  Ordo.pure (if ok then 1 else 0)

%cg native flat Runtime.OS.LinuxX86_64.release
export
release : PortTy (Service.port Service.Release)
release address bytes = do
  -- madvise(address, bytes, MADV_DONTNEED), then mprotect(address, bytes, PROT_NONE)
  _ <- Syscall.syscall 28 (ByteAddr.toWord address) bytes 4 0 0 0
  _ <- Syscall.syscall 10 (ByteAddr.toWord address) bytes 0 0 0 0
  Ordo.pure ()

%cg native flat Runtime.OS.LinuxX86_64.pageBytes
export
pageBytes : PortTy (Service.port Service.PageBytes)
pageBytes = Ordo.pure 4096

%cg native flat Runtime.OS.LinuxX86_64.stackLimit
export
stackLimit : PortTy (Service.port Service.StackLimit)
stackLimit = do
  -- getrlimit(RLIMIT_STACK, buffer): the soft limit in the buffer's first word,
  -- left 0 if the call fails
  buffer <- State.scratchArea
  Memory.storeAt buffer 0 0
  _ <- Syscall.syscall 97 3 (ByteAddr.toWord buffer) 0 0 0 0
  Memory.loadAt buffer 0

%cg native flat Runtime.OS.LinuxX86_64.prepareTerminal
export
prepareTerminal : PortTy (Service.port Service.PrepareTerminal)
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
  r <- Syscall.syscall 16 0 0x5413 (ByteAddr.toWord buffer) 0 0 0
  r' <- if failed r then Syscall.syscall 16 1 0x5413 (ByteAddr.toWord buffer) 0 0 0 else Ordo.pure r
  if failed r' then Ordo.pure 0 else Memory.loadAt buffer 0

%cg native flat Runtime.OS.LinuxX86_64.terminalColumns
export
terminalColumns : PortTy (Service.port Service.TerminalColumns)
terminalColumns = do
  size <- terminalSize
  Ordo.pure (Bits.shiftR size 16 .&. 0xFFFF)

%cg native flat Runtime.OS.LinuxX86_64.terminalLines
export
terminalLines : PortTy (Service.port Service.TerminalLines)
terminalLines = do
  size <- terminalSize
  Ordo.pure (size .&. 0xFFFF)

%cg native flat Runtime.OS.LinuxX86_64.changeDirectory
export
changeDirectory : PortTy (Service.port Service.ChangeDirectory)
changeDirectory path = do
  -- chdir(path)
  r <- Syscall.syscall 80 (ByteAddr.toWord path) 0 0 0 0 0
  ok <- succeeded r
  Ordo.pure (if ok then 1 else 0)

%cg native flat Runtime.OS.LinuxX86_64.currentDirectory
export
currentDirectory : PortTy (Service.port Service.CurrentDirectory)
currentDirectory address bytes = do
  -- getcwd(address, bytes): the path's length with its zero byte
  r <- Syscall.syscall 79 (ByteAddr.toWord address) bytes 0 0 0 0
  ok <- succeeded r
  Ordo.pure (if ok then 1 else 0)

%cg native flat Runtime.OS.LinuxX86_64.createDirectory
export
createDirectory : PortTy (Service.port Service.CreateDirectory)
createDirectory path = do
  -- mkdir(path, 0777), which the process's umask narrows
  r <- Syscall.syscall 83 (ByteAddr.toWord path) 0x1FF 0 0 0 0
  ok <- succeeded r
  Ordo.pure (if ok then 1 else 0)

%cg native flat Runtime.OS.LinuxX86_64.removeDirectory
export
removeDirectory : PortTy (Service.port Service.RemoveDirectory)
removeDirectory path = do
  -- rmdir(path)
  r <- Syscall.syscall 84 (ByteAddr.toWord path) 0 0 0 0 0
  ok <- succeeded r
  Ordo.pure (if ok then 1 else 0)

%cg native flat Runtime.OS.LinuxX86_64.openFile
export
openFile : PortTy (Service.port Service.Open)
openFile path flags = do
  -- openat(AT_FDCWD, path, flags, 0666), which the process's umask narrows;
  -- closed in a program the process runs, whose files are its own
  r <- Syscall.syscall 257 0xFFFFFFFFFFFFFF9C (ByteAddr.toWord path) (systemFlags flags) 0x1B6 0 0
  ok <- succeeded r
  Ordo.pure (if ok then r else 0xFFFFFFFFFFFFFFFF)
  where
    ||| Linux's flags for the contract's: the access, O_RDONLY, O_WRONLY or
    ||| O_RDWR, then O_CREAT, O_TRUNC, O_APPEND, O_DIRECTORY and O_CLOEXEC.
    systemFlags : Bits64 -> Bits64
    systemFlags w =
      (if OpenFlag.has OpenFlag.ForWriting w
        then (if OpenFlag.has OpenFlag.ForReading w then 2 else 1)
         else 0)
        .|. (if OpenFlag.has OpenFlag.Create w then 0x40 else 0)
        .|. (if OpenFlag.has OpenFlag.Truncate w then 0x200 else 0)
        .|. (if OpenFlag.has OpenFlag.Append w then 0x400 else 0)
        .|. (if OpenFlag.has OpenFlag.ADirectory w then 0x10000 else 0)
        .|. 0x80000

%cg native flat Runtime.OS.LinuxX86_64.close
export
close : PortTy (Service.port Service.Close)
close handle = do
  -- close(handle)
  r <- Syscall.syscall 3 handle 0 0 0 0 0
  ok <- succeeded r
  Ordo.pure (if ok then 1 else 0)

%cg native flat Runtime.OS.LinuxX86_64.read
export
read : PortTy (Service.port Service.Read)
read handle address bytes = do
  -- read(handle, address, bytes)
  r <- Syscall.syscall 0 handle (ByteAddr.toWord address) bytes 0 0 0
  ok <- succeeded r
  Ordo.pure (if ok then r else 0xFFFFFFFFFFFFFFFF)

%cg native flat Runtime.OS.LinuxX86_64.fileSize
export covering
fileSize : PortTy (Service.port Service.FileSize)
fileSize handle =
  -- fstat(handle, buffer): struct stat, 144 bytes, its st_size the word at 48
  Alloc.Block.allocate 144
    (do State.setState State.lastFailure (Failure.code Failure.NoMemory)
        Ordo.pure 0xFFFFFFFFFFFFFFFF)
    (\b => do
      let Alloc.Block.MkAddressed buffer b' = Alloc.Block.address b
      r <- Syscall.syscall 5 handle (ByteAddr.toWord buffer) 0 0 0 0
      ok <- succeeded r
      size <- Memory.loadAt buffer 48
      Alloc.Block.free b'
      Ordo.pure (if ok then size else 0xFFFFFFFFFFFFFFFF))

%cg native flat Runtime.OS.LinuxX86_64.isTerminal
export
isTerminal : PortTy (Service.port Service.IsTerminal)
isTerminal handle = do
  -- ioctl(handle, TIOCGWINSZ, buffer), which only a terminal answers; its
  -- struct winsize fits the state's scratch bytes
  buffer <- State.scratchArea
  r <- Syscall.syscall 16 handle 0x5413 (ByteAddr.toWord buffer) 0 0 0
  Ordo.pure (if failed r then 0 else 1)

%cg native flat Runtime.OS.LinuxX86_64.removeFile
export
removeFile : PortTy (Service.port Service.RemoveFile)
removeFile path = do
  -- unlink(path)
  r <- Syscall.syscall 87 (ByteAddr.toWord path) 0 0 0 0 0
  ok <- succeeded r
  Ordo.pure (if ok then 1 else 0)

%cg native flat Runtime.OS.LinuxX86_64.readEntry
export covering
readEntry : PortTy (Service.port Service.ReadEntry)
readEntry handle address bytes =
  -- getdents64(handle, buffer, 280), room for one struct linux_dirent64 of
  -- the longest name, which the system fills with the entries that fit, the
  -- first one taken: its d_off, the position after it, at 8, its name from
  -- 19; then lseek(handle, d_off, SEEK_SET), so the next read begins after it
  Alloc.Block.allocate 280
    (do State.setState State.lastFailure (Failure.code Failure.NoMemory)
        Ordo.pure 0xFFFFFFFFFFFFFFFF)
    (\b => do
      let Alloc.Block.MkAddressed buffer b' = Alloc.Block.address b
      r <- Syscall.syscall 217 handle (ByteAddr.toWord buffer) 280 0 0 0
      ok <- succeeded r
      n <- if not ok then Ordo.pure 0xFFFFFFFFFFFFFFFF else if r == 0 then Ordo.pure 0 else do
        next <- Memory.loadAt buffer 8
        _ <- Syscall.syscall 8 handle next 0 0 0 0
        name (ByteAddr.offset buffer 19) 0
      Alloc.Block.free b'
      Ordo.pure n)
  where
    -- the name's bytes from `i` copied, its zero byte too; how many before it
    covering
    name : ByteAddr -> Bits64 -> Ordo.Op Ordo Bits64
    name from i = do
      c <- Memory.loadByteAt from i
      if i + 1 >= bytes then do
          Memory.storeByteAt address i 0
          Ordo.pure i
        else do
          Memory.storeByteAt address i c
          if c == 0 then Ordo.pure i else name from (i + 1)
