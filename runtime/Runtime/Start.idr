||| The program's start-up: what the runtime sets up before `main`. The
||| entry the system jumps to, `_start`, calls `start` with the stack pointer
||| it was given and the allocation window's size, then enters `main` as the
||| lowering of continuations enters code.
module Runtime.Start

import public Runtime.Memory

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| The most of the process stack direct code may use, whatever the stack's
||| limit: 1 GiB.
stackCap : Bits64
stackCap = 1073741824

||| What the stack check leaves below the limit, for the arguments and the
||| environment above the stack pointer at entry and for the frames of code
||| that does not check, such as a direct call's saved values: 256 KiB.
stackMargin : Bits64
stackMargin = 262144

||| The stack's limit assumed when the system does not say: Linux's
||| default, 8 MiB.
defaultStack : Bits64
defaultStack = 8388608

%cg native flat Runtime.Start.start
||| `idris_start`: the first allocation window, mapped, of `window` bytes;
||| the stack limit, which direct code, deepened by recursion in flat code,
||| checks on entry: the stack pointer at entry less the stack's limit, at
||| most `stackCap`, plus `stackMargin`, so that recursion too deep ends with
||| a message before the system's guard gap faults; and the stack pointer at
||| entry, `entry`, kept for the program's arguments.
export
start : (entry, window : Bits64) -> Op Heap ()
start entry window = do
  w <- mapMemory {k = BUFFER} window
  -- the window's first 16 bytes lent to getrlimit, then zeroed again
  soft <- stackSoftLimit w defaultStack
  store64 w 0 0
  store64 w 8 0
  limit <- stackLimitArea {k = BUFFER}
  store64 limit 0 (entry - (if soft > stackCap then stackCap else soft) + stackMargin)
  argv <- argvArea {k = BUFFER}
  store64 argv 0 entry
  setWindow w window
