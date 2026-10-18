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

import Native.HeapObj.Shape
import Native.Port
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
  Ordo.pure (if failed r then 0 else r)

%cg native flat Runtime.OS.LinuxX86_64.reserve
export
reserve : PortTy Memory.Addr (Service.port Service.Reserve)
reserve bytes = do
  -- mmap(NULL, bytes, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0):
  -- no overcommit setting counts a range that is not readable
  r <- Syscall.syscall 9 0 bytes 0 0x4022 0xFFFFFFFFFFFFFFFF 0
  -- the system gives the range's address as a word
  Ordo.pure (Raw.fromWord (if failed r then 0 else r))

%cg native flat Runtime.OS.LinuxX86_64.commit
export
commit : PortTy Memory.Addr (Service.port Service.Commit)
commit address bytes = do
  -- mprotect(address, bytes, PROT_READ | PROT_WRITE): the pages are zero when first touched
  r <- Syscall.syscall 10 (Raw.rawWord address) bytes 3 0 0 0
  Ordo.pure (if r == 0 then 1 else 0)

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
