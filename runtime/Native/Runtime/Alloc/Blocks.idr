||| An array of owned blocks, kept in a word of the runtime's state
||| (`Blocks`): the blocks go in and come out linearly, one at a time, and
||| the array itself never leaves its word, so nothing but this module holds
||| it. Part of the allocator's sealed modules, the only one that keeps a
||| block's address in memory.
|||
||| The array is a block of its own: its count of blocks at 0, the blocks it
||| has room for at 8, then the address of each block, from 16. It is made
||| on demand (`make`), grows by doubling when a block goes in and it is
||| full, and is freed with every block it holds (`dispose`). A block goes
||| in by `push`; one comes out by `replace` or `removeAt`, to a function
||| that is to use it, as a block is used; `at` reads where one is, which
||| the array keeps.
|||
||| Each array is one this module names, in a word of the state it reserves
||| for it: no other code makes one, so none is held twice.
module Native.Runtime.Alloc.Blocks

import Native.Runtime.Alloc.Block
import Native.Runtime.Alloc.System
import Native.Runtime.Memory
import Native.Runtime.Ordo
import Native.Runtime.Raw
import Native.Runtime.State

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| An array of owned blocks, by the word of the state that holds its
||| address, null until it is made.
export
data Blocks : Type where
  MkBlocks : State Raw -> Blocks

||| The environment's entries (`Support.Environment`), once the program
||| changes it.
export
environment : Blocks
environment = MkBlocks State.environArray

||| The array's address, null if it is not made.
arrayOf : Blocks -> Op Ordo Raw
arrayOf (MkBlocks s) = State.getState s

||| Where block `i`'s address is in the array.
slot : (i : Bits64) -> Bits64
slot i = 16 + 8 * i

||| Whether the array is made.
export
made : Blocks -> Op Ordo Bool
made xs = do
  a <- arrayOf xs
  pure (not (Raw.isNull a))

||| The array made, empty, with room for `capacity` blocks, if it is not
||| yet; whether it is, which it is not if there is no memory for it.
export covering
make : Blocks -> (capacity : Bits64) -> Op Ordo Bool
make xs@(MkBlocks s) capacity = do
  a <- arrayOf xs
  if not (Raw.isNull a) then pure True else do
    w <- System.allocateBlock (slot capacity)
    if w == 0 then pure False else do
      let r = Memory.foreignBytes w
      Memory.storeAt r 0 0
      Memory.storeAt r 8 capacity
      State.setState s r
      pure True

||| How many blocks the array holds, 0 if it is not made.
export
size : Blocks -> Op Ordo Bits64
size xs = do
  a <- arrayOf xs
  if Raw.isNull a then pure 0 else Memory.loadAt a 0

||| Where block `i` is, which the array keeps; the program ends for an `i`
||| the array has no block for.
export
at : Blocks -> (i : Bits64) -> Op Ordo Raw
at xs i = do
  a <- arrayOf xs
  n <- if Raw.isNull a then pure 0 else Memory.loadAt a 0
  if i >= n then crashOp "idris: a block the array does not hold" else do
    w <- Memory.loadAt a (slot i)
    pure (Memory.foreignBytes w)

||| The block put last in the array, which grows when it is full, then
||| `done`; `none` of the block if there is no memory for the array to grow,
||| or the array is not made.
export %inline covering
push : Blocks -> (1 b : Block) -> (none : (1 b : Block) -> Op Ordo a) -> (done : Op Ordo a) -> Op Ordo a
push xs b none done = do
  ok <- room xs
  case ok of
    True => do
      r <- Block.releaseBlock b
      a <- arrayOf xs
      n <- Memory.loadAt a 0
      Memory.storeAt a (slot n) (Raw.rawWord r)
      Memory.storeAt a 0 (n + 1)
      done
    False => none b
  where
    ||| Room for one block more, the array grown if it is full: a new one of
    ||| twice the room, the addresses copied, the old one freed. Whether
    ||| there is.
    covering
    room : Blocks -> Op Ordo Bool
    room xs@(MkBlocks s) = do
      a <- arrayOf xs
      if Raw.isNull a then pure False else do
        n <- Memory.loadAt a 0
        c <- Memory.loadAt a 8
        if n < c then pure True else do
          w <- System.allocateBlock (slot (2 * c))
          if w == 0 then pure False else do
            let r = Memory.foreignBytes w
            Memory.copyRaw a r (slot n)
            Memory.storeAt r 8 (2 * c)
            System.freeBlock (Raw.rawWord a)
            State.setState s r
            pure True

||| Block `i` replaced by `b`, and given to `k`; the program ends for an `i`
||| the array has no block for.
export %inline covering
replace : Blocks -> (i : Bits64) -> (1 b : Block) -> (k : (1 old : Block) -> Op Ordo a) -> Op Ordo a
replace xs i b k = do
  _ <- at xs i
  a <- arrayOf xs
  old <- Memory.loadAt a (slot i)
  r <- Block.releaseBlock b
  Memory.storeAt a (slot i) (Raw.rawWord r)
  k (Block.adoptBlock (Memory.foreignBytes old))

||| Block `i` taken out of the array, the last moved into its place, and
||| given to `k`; the program ends for an `i` the array has no block for.
export %inline covering
removeAt : Blocks -> (i : Bits64) -> (k : (1 old : Block) -> Op Ordo a) -> Op Ordo a
removeAt xs i k = do
  _ <- at xs i
  a <- arrayOf xs
  n <- Memory.loadAt a 0
  old <- Memory.loadAt a (slot i)
  last <- Memory.loadAt a (slot (n - 1))
  Memory.storeAt a (slot i) last
  Memory.storeAt a 0 (n - 1)
  k (Block.adoptBlock (Memory.foreignBytes old))

||| Every block of the array freed, and the array: not made again until
||| `make`.
export covering
dispose : Blocks -> Op Ordo ()
dispose xs@(MkBlocks s) = do
  a <- arrayOf xs
  if Raw.isNull a then pure () else do
    n <- Memory.loadAt a 0
    freeAll a 0 n
    System.freeBlock (Raw.rawWord a)
    State.setState s (Memory.foreignBytes 0)
  where
    covering
    freeAll : Raw -> (i, n : Bits64) -> Op Ordo ()
    freeAll a i n = if i >= n then pure () else do
      w <- Memory.loadAt a (slot i)
      System.freeBlock w
      freeAll a (i + 1) n
