-- The runtime's blocks of memory outside the heap are linear: each block
-- is used exactly once, so Idris rejects a program that drops one, frees
-- one twice, or frees one on one branch and not the other. This file
-- typechecks exactly when each `failing` block fails, for the reason it
-- names, and the rest checks.
--
-- A block comes from `allocate`, which runs a function of it, or something
-- else when there is no memory; `address` gives its bytes and the block
-- back, still to be used; `free` uses it up. In surface Idris, with the
-- token the runtime threads (`Ordo`) left implicit, as `do` leaves it:
--
--     allocate 64 (pure 0) (\b => do
--       let MkAddressed bytes b' = address b   -- b is used; b' is the block now
--       storeAt bytes 0 7
--       free b'                                -- b' is used
--       pure 1)
--
-- `do` keeps a block linear across its steps because the token's bind uses
-- each of its operands once. A choice between two uses is a `case`: the
-- branches of `if` are lazy, and so might run any number of times.
--
-- An array of owned blocks (`Blocks`) takes a block in and gives one out
-- the same way: `push` uses the block up, or gives it back to `none` when
-- there is no memory; `replace` and `removeAt` give the block they take out
-- to a function, which has to use it as any block.
module Owned

import Native.Runtime.Alloc.Block
import Native.Runtime.Alloc.Blocks
import Native.Runtime.Memory
import Native.Runtime.Ordo

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default covering

-- allocated, written, freed
used : Op Ordo Bits64
used = allocate 64 (pure 0) (\b => do
  let MkAddressed bytes b' = address b
  storeAt bytes 0 7
  free b'
  pure 1)

-- freed on each branch
eachBranch : Bits64 -> Op Ordo Bits64
eachBranch n = allocate 64 (pure 0) (\b => case n == 0 of
  True => do
    free b
    pure 1
  False => do
    free b
    pure 2)

failing "There are 0 uses of linear name b'"
  -- the block is never freed
  dropped : Op Ordo Bits64
  dropped = allocate 64 (pure 0) (\b => do
    let MkAddressed bytes b' = address b
    loadAt bytes 0)

failing "There are 2 uses of linear name b"
  -- the block is freed twice
  twice : Op Ordo ()
  twice = allocate 64 (pure ()) (\b => do
    free b
    free b)

failing "Inconsistent usage of b in case branches"
  -- the block is freed on one branch only
  oneBranch : Bits64 -> Op Ordo ()
  oneBranch n = allocate 64 (pure ()) (\b => case n == 0 of
    True => free b
    False => pure ())

failing "b is not accessible in this context"
  -- the block's address read twice from the same name: `address` uses the
  -- block up and gives it back under a new name, and the old one is spent
  reused : Op Ordo Bits64
  reused = allocate 64 (pure 0) (\b => do
    let MkAddressed bytes b' = address b
    let MkAddressed bytes' b'' = address b
    free b'
    free b''
    pure 0)

-- a block put in the array, or freed if it cannot be
kept : Op Ordo Bool
kept = allocate 64 (pure False) (\b =>
  push environment b
    (\b' => do
      free b'
      pure False)
    (pure True))

-- the block an array gives back, freed
swapped : Op Ordo ()
swapped = allocate 64 (pure ()) (\b =>
  replace environment 0 b (\old => free old))

failing "There are 0 uses of linear name old"
  -- the block `replace` gives back is dropped
  lost : Op Ordo ()
  lost = allocate 64 (pure ()) (\b =>
    replace environment 0 b (\old => pure ()))

failing "There are 0 uses of linear name b'"
  -- the block `push` gives back when there is no memory is dropped
  unkept : Op Ordo ()
  unkept = allocate 64 (pure ()) (\b =>
    push environment b (\b' => pure ()) (pure ()))

failing "There are 0 uses of linear name old"
  -- the block `removeAt` takes out is dropped
  removed : Op Ordo ()
  removed = removeAt environment 0 (\old => pure ())

failing "MkBlock is private"
  -- a block cannot be made but by `allocate`
  forged : Block
  forged = MkBlock 4096
