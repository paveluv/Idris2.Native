||| The program's start-up: what the runtime sets up before `main`. The
||| entry the system jumps to, `_start`, calls `start` with the stack pointer
||| it was given and the allocation window's size, then enters `main` as the
||| lowering of continuations enters code.
module Runtime.Start

import public Runtime.Space

import Runtime.Bits

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

||| A space's reservation: as large as the system allows, from 32 TiB
||| halving to 64 MiB, so that only the system, or a limit the user set on
||| the process's address space, bounds the heap. Its address and size.
covering
reserveSpace : (bytes : Bits64) -> Op Heap (Bits64, Bits64)
reserveSpace bytes =
  if bytes < 67108864 then crashOp "idris: cannot reserve memory" else do
    a <- reserveMemory bytes
    if a == 0 then reserveSpace (shiftR bytes 1) else pure (a, bytes)

%cg native flat Runtime.Start.start
||| `idris_start`: the two spaces reserved and the first window committed,
||| of `window` bytes, as the allocation window; the stack limit, which
||| direct code, deepened by recursion in flat code, checks on entry: the
||| stack pointer at entry less the stack's limit, at most `stackCap`, plus
||| `stackMargin`, so that recursion too deep ends with a message before the
||| system's guard gap faults; and the stack pointer at entry, `entry`, kept
||| for the program's arguments.
export covering
start : (entry, window : Bits64) -> Op Heap ()
start entry window = do
  (fb, fs) <- reserveSpace 35184372088832
  (tb, ts) <- reserveSpace 35184372088832
  setState fromBase fb
  setState fromEnd (fb + fs)
  setState fromCommitted fb
  setState toBase tb
  setState toEnd (tb + ts)
  setState toCommitted tb
  setState toTop tb
  setState scanCursor tb
  setState liveBytes 0
  setState heapLimit 0
  setState windowBytes window
  setState collections 0
  firstEnd <- roundToPage (fb + window)
  commitMemory fb (firstEnd - fb)
  setState fromCommitted firstEnd
  setAllocation fb (fb + window)
  given <- osStackLimit
  let soft = if given == 0 then defaultStack else given
  limit <- stackLimitArea {k = BUFFER}
  store64 limit 0 (entry - (if soft > stackCap then stackCap else soft) + stackMargin)
  argv <- argvArea {k = BUFFER}
  store64 argv 0 entry
