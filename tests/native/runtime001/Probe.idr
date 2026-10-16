-- Flat code over raw memory, written as the runtime is: with the runtime
-- library's own operations, imported here as a package. The runtime has no
-- monad and no `IO`. Each operation takes the token `Heap` and returns it
-- with its value, and the `do` below is the runtime's own bind over that
-- shape, so the operations happen in the order they are written: a load
-- after a store sees the store. The token takes no register, so the order
-- costs nothing.
--
-- `mapMemory` asks the system for a page; `store64` and `load64` write and
-- read a word at an address plus a byte offset; the narrow ones the low 8,
-- 16 or 32 bits, read back with zeros above. Each is an intrinsic: in the
-- flat lowering it is the one instruction it stands for, never a call.
module Probe

-- the runtime's functions use its own bit operations, which it does not
-- re-export; flat code that reaches into them imports those too
import Native.Heap
import Native.HeapObj.Shape
import Native.Runtime.Bits
import Native.Runtime.Memory

-- this module's `do` is the runtime's, over the token
%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| 0 if the check holds, 1 if not, so that failures add up.
failed : Bool -> Bits64
failed b = if b then 0 else 1

||| Write a page at several widths and read it back: the number of checks
||| that fail.
checks : (x : Bits64) -> Op Heap Bits64
checks x = do
  a <- mapMemory {s = RAW} 4096
  store64 a 0 x
  store64 a 8 (x * 2)
  store8 a 16 0x1FF                -- only its low byte, 0xFF, is stored
  store16 a 24 0x12345             -- 0x2345
  store32 a 32 0x123456789         -- 0x23456789
  w0 <- load64 a 0
  w1 <- load64 a 8
  b <- load8 a 16
  h <- load16 a 24
  q <- load32 a 32
  z <- load64 a 40                 -- never written: the system zeroed it
  -- a byte over the word at 0: little-endian, so it replaces the lowest
  store8 a 0 0xAA
  w0' <- load64 a 0
  pure (failed (w0 == x) + failed (w1 == x * 2) + failed (b == 0xFF)
        + failed (h == 0x2345) + failed (q == 0x23456789) + failed (z == 0)
        + failed (w0' == (x - x `mod` 256) + 0xAA))

-- As a flat function, as if written
--
--   probe : Bits64 -> Bits64
--
-- with the token made here and dropped when the checks are done.
%cg native flat Probe.probe
export
probe : Bits64 -> Bits64
probe x = let (MkHeap # r) = checks x MkHeap in r
