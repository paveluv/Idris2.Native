||| The OS services on x86-64 Linux, by raw system calls. Linux keeps a
||| stable system-call ABI: the number in rax and the arguments in rdi, rsi,
||| rdx, r10, r8 and r9, the result in rax, an error as a number from -4095
||| to -1. The numbers here are x86-64's; another architecture's Linux has
||| its own. This module's record of them (`services`) is what the native
||| code generator binds the services' externs (`Native.Services`) to when a
||| program is compiled for x86-64 Linux, and it loads this module for it;
||| nothing in the generic runtime imports it.
module Native.Runtime.OS.LinuxX86_64

import Native.Runtime.OS.Syscall

import Native.Heap
import Native.HeapObj.Shape as HeapObj
import Native.Port
import Native.Runtime.Memory
import Native.Runtime.State
import Native.Services

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| Whether a system call's result is an error.
failed : Bits64 -> Bool
failed r = r > 0xFFFFFFFFFFFFF000

%cg native flat Runtime.OS.LinuxX86_64.exit
export
exit : (status : Bits64) -> Heap.Op Heap ()
exit status = do
  -- exit_group(status)
  _ <- Syscall.syscall 231 status 0 0 0 0 0
  Heap.pure ()

%cg native flat Runtime.OS.LinuxX86_64.write
export
write : (handle, address, bytes : Bits64) -> Heap.Op Heap Bits64
write handle address bytes = do
  -- write(handle, address, bytes)
  r <- Syscall.syscall 1 handle address bytes 0 0 0
  Heap.pure (if failed r then 0 else r)

%cg native flat Runtime.OS.LinuxX86_64.reserve
export
reserve : (bytes : Bits64) -> Heap.Op Heap Bits64
reserve bytes = do
  -- mmap(NULL, bytes, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0):
  -- no overcommit setting counts a range that is not readable
  r <- Syscall.syscall 9 0 bytes 0 0x4022 0xFFFFFFFFFFFFFFFF 0
  Heap.pure (if failed r then 0 else r)

%cg native flat Runtime.OS.LinuxX86_64.commit
export
commit : (address, bytes : Bits64) -> Heap.Op Heap Bits64
commit address bytes = do
  -- mprotect(address, bytes, PROT_READ | PROT_WRITE): the pages are zero when first touched
  r <- Syscall.syscall 10 address bytes 3 0 0 0
  Heap.pure (if r == 0 then 1 else 0)

%cg native flat Runtime.OS.LinuxX86_64.release
export
release : (address, bytes : Bits64) -> Heap.Op Heap ()
release address bytes = do
  -- madvise(address, bytes, MADV_DONTNEED), then mprotect(address, bytes, PROT_NONE)
  _ <- Syscall.syscall 28 address bytes 4 0 0 0
  _ <- Syscall.syscall 10 address bytes 0 0 0 0
  Heap.pure ()

%cg native flat Runtime.OS.LinuxX86_64.pageBytes
export
pageBytes : Heap.Op Heap Bits64
pageBytes = Heap.pure 4096

%cg native flat Runtime.OS.LinuxX86_64.stackLimit
export
stackLimit : Heap.Op Heap Bits64
stackLimit = do
  -- getrlimit(RLIMIT_STACK, buffer): the soft limit in the buffer's first word,
  -- left 0 if the call fails
  buffer <- State.scratchArea
  Memory.storeAt buffer 0 0
  _ <- Syscall.syscall 97 3 buffer 0 0 0 0
  Memory.loadAt buffer 0

||| The services on x86-64 Linux, each checked against its port: the
||| record the code generator binds `Native.Services`'s externs to.
export
services : Services (Port.PortTy (\s => Memory.Addr s))
services =
  MkServices
    { exit = LinuxX86_64.exit, write = LinuxX86_64.write, reserve = LinuxX86_64.reserve
    , commit = LinuxX86_64.commit, release = LinuxX86_64.release
    , stackLimit = LinuxX86_64.stackLimit, pageBytes = LinuxX86_64.pageBytes }
