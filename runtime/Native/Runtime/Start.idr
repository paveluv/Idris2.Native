||| The program's start-up: what the runtime sets up before `main`. The
||| entry the system jumps to, `_start`, calls `start` with the stack pointer
||| it was given and the allocation window's size, then enters `main` as the
||| lowering of continuations enters code.
module Native.Runtime.Start

import Native.Runtime.Bits
import Native.Runtime.ByteAddr
import Native.Runtime.Cell
import Native.Runtime.Memory
import Native.Runtime.Ordo
import Native.Runtime.OS
import Native.Runtime.PortTy
import Native.Runtime.State

import Native.Carrier
import Native.Routine

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

%cg native flat Runtime.Start.start
||| `idris_start`: the two spaces reserved and the first window committed,
||| of `window` bytes, as the allocation window; the stack limit, which
||| direct code, deepened by recursion in flat code, checks on entry: the
||| stack pointer at entry less the stack's limit, at most `stackCap`, plus
||| `stackMargin`, so that recursion too deep ends with a message before the
||| system's guard gap faults; and the stack pointer at entry, `entry`, kept
||| for the program's arguments.
export covering
start : PortTy (Routine.port Routine.Start)
start entry window = do
  (fb, fs) <- reserveSpace 35184372088832
  (tb, ts) <- reserveSpace 35184372088832
  State.setState State.fromBase fb
  State.setState State.fromEnd (ByteAddr.offset fb fs)
  State.setState State.fromCommitted fb
  State.setState State.toBase tb
  State.setState State.toEnd (ByteAddr.offset tb ts)
  State.setState State.toCommitted tb
  State.setState State.toTop tb
  State.setState State.scanCursor tb
  State.setState State.liveBytes 0
  State.setState State.heapLimit 0
  State.setState State.windowBytes window
  State.setState State.collections 0
  firstEnd <- Memory.alignToPage (ByteAddr.offset fb window)
  Memory.commitMemory fb (ByteAddr.distance firstEnd fb)
  State.setState State.fromCommitted firstEnd
  Memory.setAllocation fb (ByteAddr.offset fb window)
  given <- OS.osStackLimit
  let soft = if given == 0 then defaultStack else given
  limit <- Memory.stackLimitArea
  Memory.storeAt limit 0
    (ByteAddr.toWord
      (ByteAddr.offset (ByteAddr.before entry (if soft > stackCap then stackCap else soft))
        stackMargin))
  argv <- Memory.argvArea
  Memory.storeAt argv 0 (ByteAddr.toWord entry)
  where
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
    reserveSpace : (bytes : Bits64) -> Ordo.Op Ordo (ByteAddr, Bits64)
    reserveSpace bytes =
      if bytes < 67108864 then Ordo.crashOp "idris: cannot reserve memory" else do
        a <- Memory.reserveMemory bytes
        if ByteAddr.isNull a then reserveSpace (Bits.shiftR bytes 1) else Ordo.pure (a, bytes)
