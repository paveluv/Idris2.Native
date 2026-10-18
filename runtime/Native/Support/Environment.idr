||| The process's environment: its entries, each the address of the bytes
||| `NAME=value` and a zero byte, as C's `environ` holds them.
|||
||| Until the program changes it, the environment is the one the system gave,
||| after the arguments (`Memory.environmentEntry`). The first change copies
||| the entries' addresses into an array of the runtime's own, in memory
||| outside the heap (`Runtime.Alloc.Block`), its address and its count in
||| the runtime's state; the entries themselves stay where they are. A
||| variable set is a new entry there; an entry replaced or removed is never
||| freed, so that a pointer `getEnv` gave stays valid, as the C library's
||| does. The array grows by doubling, the old one freed: no pointer into it
||| is ever given out.
|||
||| Names and values come as bytes and counts, so that this module reads no
||| string: the string module (`Support.String.Utf8`) gives them.
module Native.Support.Environment

import Native.Runtime.Alloc.Block
import Native.Runtime.Memory
import Native.Runtime.Ordo as Runtime
import Native.Runtime.Raw
import Native.Runtime.State

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| The address of entry `n`, a word; 0 past the last.
export covering
entryAt : (n : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bits64
entryAt n = do
  arr <- Runtime.State.getState Runtime.State.environArray
  if Runtime.Raw.isNull arr then Runtime.Memory.environmentEntry n else do
    count <- Runtime.State.getState Runtime.State.environCount
    if n >= count then Runtime.Ordo.pure 0 else Runtime.Memory.loadAt arr (8 * n)

||| The index of the first entry of the name, if there is one.
export covering
find : (name : Raw) -> (len : Bits64) -> Runtime.Ordo.Op Runtime.Ordo (Maybe Bits64)
find name len = go 0
  where
    ||| Whether the entry at `e` holds the name's `len` bytes, then `=`.
    covering
    holds : (name : Raw) -> (len, e : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bool
    holds name len e = go 0
      where
        covering
        go : Bits64 -> Runtime.Ordo.Op Runtime.Ordo Bool
        go i = do
          b <- Runtime.Memory.loadByteAt (Runtime.Memory.foreignBytes e) i
          if i == len then Runtime.Ordo.pure (b == 0x3D) else do
            c <- Runtime.Memory.loadByteAt name i
            if b /= c then Runtime.Ordo.pure False else go (i + 1)

    covering
    go : Bits64 -> Runtime.Ordo.Op Runtime.Ordo (Maybe Bits64)
    go n = do
      e <- entryAt n
      if e == 0 then Runtime.Ordo.pure Nothing else do
        found <- holds name len e
        if found then Runtime.Ordo.pure (Just n) else go (n + 1)

||| Whether a name can be a variable's: not empty, and without `=` or a
||| zero byte, which would end it in an entry, as the C library's `setenv`
||| refuses.
covering
validName : (name : Raw) -> (len : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bool
validName name len = if len == 0 then Runtime.Ordo.pure False else go 0
  where
    covering
    go : Bits64 -> Runtime.Ordo.Op Runtime.Ordo Bool
    go i = if i >= len then Runtime.Ordo.pure True else do
      c <- Runtime.Memory.loadByteAt name i
      if c == 0x3D || c == 0 then Runtime.Ordo.pure False else go (i + 1)

||| The environment made the runtime's own, if it is not yet: the system's
||| entries copied into an array with room for more. Whether there was the
||| memory for it.
covering
own : Runtime.Ordo.Op Runtime.Ordo Bool
own = do
  arr <- Runtime.State.getState Runtime.State.environArray
  if not (Runtime.Raw.isNull arr) then Runtime.Ordo.pure True else do
    count <- counted 0
    let room = count + 16
    Runtime.Alloc.Block.allocate (8 * room) (Runtime.Ordo.pure False) (\b => do
      let MkAddressed a b' = Runtime.Alloc.Block.address b
      copyEntries a 0 count
      -- lint: allow sealed-allocator: the array is the environment's, in the state, until `append` grows it and frees it
      w <- Runtime.Alloc.Block.releaseBlock b'
      Runtime.State.setState Runtime.State.environArray w
      Runtime.State.setState Runtime.State.environCount count
      Runtime.State.setState Runtime.State.environCapacity room
      Runtime.Ordo.pure True)
  where
    covering
    counted : Bits64 -> Runtime.Ordo.Op Runtime.Ordo Bits64
    counted n = do
      e <- Runtime.Memory.environmentEntry n
      if e == 0 then Runtime.Ordo.pure n else counted (n + 1)

    covering
    copyEntries : (to : Raw) -> (i, n : Bits64) -> Runtime.Ordo.Op Runtime.Ordo ()
    copyEntries to i n = if i >= n then Runtime.Ordo.pure () else do
      e <- Runtime.Memory.environmentEntry i
      Runtime.Memory.storeAt to (8 * i) e
      copyEntries to (i + 1) n

||| `setenv`: the variable of the name set to the value, unless it is set
||| and `overwrite` is false; whether it is, which it is not for a name
||| that cannot be a variable's (`validName`) or when there is no memory.
export covering
set : (name : Raw) -> (nameLen : Bits64) -> (value : Raw) -> (valueLen : Bits64) -> (overwrite : Bool) ->
      Runtime.Ordo.Op Runtime.Ordo Bool
set name nl value vl overwrite = do
  valid <- validName name nl
  if not valid then Runtime.Ordo.pure False else do
    found <- find name nl
    case found of
      Just i =>
        if not overwrite then Runtime.Ordo.pure True else do
          ok <- own
          e <- if ok then newEntry name nl value vl else Runtime.Ordo.pure 0
          if e == 0 then Runtime.Ordo.pure False else do
            arr <- Runtime.State.getState Runtime.State.environArray
            Runtime.Memory.storeAt arr (8 * i) e
            Runtime.Ordo.pure True
      Nothing => do
        ok <- own
        e <- if ok then newEntry name nl value vl else Runtime.Ordo.pure 0
        if e == 0 then Runtime.Ordo.pure False else append e
  where
    ||| A new entry, `NAME=value` and a zero byte, in memory outside the heap:
    ||| its address, 0 if there is no memory for it.
    covering
    newEntry : (name : Raw) -> (nameLen : Bits64) -> (value : Raw) -> (valueLen : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bits64
    newEntry name nl value vl =
      Runtime.Alloc.Block.allocate (nl + vl + 2) (Runtime.Ordo.pure 0) (\b => do
        let MkAddressed e b' = Runtime.Alloc.Block.address b
        Runtime.Memory.copyRaw name e nl
        Runtime.Memory.storeByteAt e nl 0x3D
        Runtime.Memory.copyRaw value (Runtime.Raw.offset e (nl + 1)) vl
        Runtime.Memory.storeByteAt e (nl + 1 + vl) 0
        -- lint: allow sealed-allocator: an entry is the environment's for good, so that getEnv's pointers into it stay valid
        a <- Runtime.Alloc.Block.releaseBlock b'
        Runtime.Ordo.pure (Runtime.Raw.rawWord a))

    ||| An entry put last in the runtime's array, which grows when it is full:
    ||| whether there was the memory for it.
    covering
    append : (e : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bool
    append e = do
      arr <- Runtime.State.getState Runtime.State.environArray
      count <- Runtime.State.getState Runtime.State.environCount
      room <- Runtime.State.getState Runtime.State.environCapacity
      if count < room
         then do
           Runtime.Memory.storeAt arr (8 * count) e
           Runtime.State.setState Runtime.State.environCount (count + 1)
           Runtime.Ordo.pure True
         else
           Runtime.Alloc.Block.allocate (16 * room) (Runtime.Ordo.pure False) (\b => do
             let MkAddressed a b' = Runtime.Alloc.Block.address b
             copyWords arr a 0 count
             -- lint: allow sealed-allocator: the array in the state is the one `own` or the last growth released there, which nothing else holds
             Runtime.Alloc.Block.free (Runtime.Alloc.Block.adoptBlock arr)
             -- lint: allow sealed-allocator: the array is the environment's, in the state, until the next growth frees it
             w <- Runtime.Alloc.Block.releaseBlock b'
             Runtime.State.setState Runtime.State.environArray w
             Runtime.State.setState Runtime.State.environCapacity (2 * room)
             append e)
      where
        covering
        copyWords : (from, to : Raw) -> (i, n : Bits64) -> Runtime.Ordo.Op Runtime.Ordo ()
        copyWords from to i n = if i >= n then Runtime.Ordo.pure () else do
          w <- Runtime.Memory.loadAt from (8 * i)
          Runtime.Memory.storeAt to (8 * i) w
          copyWords from to (i + 1) n

||| `unsetenv`: every entry of the name removed, the last entry moved into
||| each one's place; whether the name can be a variable's.
export covering
unset : (name : Raw) -> (nameLen : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bool
unset name nl = do
  valid <- validName name nl
  if not valid then Runtime.Ordo.pure False else go
  where
    covering
    go : Runtime.Ordo.Op Runtime.Ordo Bool
    go = do
      found <- find name nl
      case found of
        Nothing => Runtime.Ordo.pure True
        Just i => do
          ok <- own
          if not ok then Runtime.Ordo.pure False else do
            arr <- Runtime.State.getState Runtime.State.environArray
            count <- Runtime.State.getState Runtime.State.environCount
            last <- Runtime.Memory.loadAt arr (8 * (count - 1))
            Runtime.Memory.storeAt arr (8 * i) last
            Runtime.State.setState Runtime.State.environCount (count - 1)
            go
