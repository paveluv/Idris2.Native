||| The process's environment: its entries, each the address of the bytes
||| `NAME=value` and a zero byte, as C's `environ` holds them.
|||
||| Until the program changes it, the environment is the one the system gave,
||| after the arguments (`Memory.environmentEntry`). The first change copies
||| each entry into a block of its own, kept in the runtime's array of the
||| environment's blocks (`Runtime.Alloc.Blocks.environment`), all of them
||| or, if there is not the memory, none. A variable set is a new block
||| there; an entry replaced or removed is freed. Nothing holds a pointer
||| into one past the call that gave it: `base` copies what `getEnv` points
||| at before it does anything else, and no C code is linked to keep one,
||| so the runtime frees what the C library has to keep for good.
|||
||| Names and values come as bytes and counts, so that this module reads no
||| string: the string module (`Support.String.Utf8`) gives them.
module Native.Support.Environment

import Native.Runtime.Alloc.Block
import Native.Runtime.Alloc.Blocks
import Native.Runtime.Memory
import Native.Runtime.Ordo as Runtime
import Native.Runtime.Raw

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| The address of entry `n`, a word; 0 past the last.
export covering
entryAt : (n : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bits64
entryAt n = do
  owned <- Runtime.Alloc.Blocks.made Runtime.Alloc.Blocks.environment
  if not owned then Runtime.Memory.environmentEntry n else do
    count <- Runtime.Alloc.Blocks.size Runtime.Alloc.Blocks.environment
    if n >= count then Runtime.Ordo.pure 0 else do
      e <- Runtime.Alloc.Blocks.at Runtime.Alloc.Blocks.environment n
      Runtime.Ordo.pure (Runtime.Raw.rawWord e)

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

||| The environment made the runtime's own, if it is not yet: each of the
||| system's entries copied into a block, in an array with room for more.
||| Whether there was the memory for it; if not, nothing is kept.
covering
own : Runtime.Ordo.Op Runtime.Ordo Bool
own = do
  owned <- Runtime.Alloc.Blocks.made Runtime.Alloc.Blocks.environment
  if owned then Runtime.Ordo.pure True else do
    count <- counted 0
    ok <- Runtime.Alloc.Blocks.make Runtime.Alloc.Blocks.environment (count + 16)
    if not ok then Runtime.Ordo.pure False else copyAll 0 count
  where
    covering
    counted : Bits64 -> Runtime.Ordo.Op Runtime.Ordo Bits64
    counted n = do
      e <- Runtime.Memory.environmentEntry n
      if e == 0 then Runtime.Ordo.pure n else counted (n + 1)

    -- the bytes of an entry before its zero byte
    covering
    lengthOf : Raw -> (i : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bits64
    lengthOf e i = do
      c <- Runtime.Memory.loadByteAt e i
      if c == 0 then Runtime.Ordo.pure i else lengthOf e (i + 1)

    -- what was copied given up, as there is not the memory for the rest
    covering
    noMemory : Runtime.Ordo.Op Runtime.Ordo Bool
    noMemory = do
      Runtime.Alloc.Blocks.dispose Runtime.Alloc.Blocks.environment
      Runtime.Ordo.pure False

    covering
    copyAll : (i, n : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bool
    copyAll i n = if i >= n then Runtime.Ordo.pure True else do
      w <- Runtime.Memory.environmentEntry i
      let e = Runtime.Memory.foreignBytes w
      len <- lengthOf e 0
      Runtime.Alloc.Block.allocate (len + 1) noMemory (\b => do
        let MkAddressed p b' = Runtime.Alloc.Block.address b
        Runtime.Memory.copyRaw e p (len + 1)
        Runtime.Alloc.Blocks.push Runtime.Alloc.Blocks.environment b'
          (\b'' => do
            Runtime.Alloc.Block.free b''
            noMemory)
          (copyAll (i + 1) n))

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
          if not ok then Runtime.Ordo.pure False else
            newEntry (Runtime.Ordo.pure False) (\e =>
              Runtime.Alloc.Blocks.replace Runtime.Alloc.Blocks.environment i e (\old => do
                Runtime.Alloc.Block.free old
                Runtime.Ordo.pure True))
      Nothing => do
        ok <- own
        if not ok then Runtime.Ordo.pure False else
          newEntry (Runtime.Ordo.pure False) (\e =>
            Runtime.Alloc.Blocks.push Runtime.Alloc.Blocks.environment e
              (\e' => do
                Runtime.Alloc.Block.free e'
                Runtime.Ordo.pure False)
              (Runtime.Ordo.pure True))
  where
    ||| A new entry, `NAME=value` and a zero byte, in a block for `use`;
    ||| `none` if there is no memory for it.
    %inline covering
    newEntry : (none : Runtime.Ordo.Op Runtime.Ordo Bool) -> (use : (1 e : Block) -> Runtime.Ordo.Op Runtime.Ordo Bool) ->
               Runtime.Ordo.Op Runtime.Ordo Bool
    newEntry none use =
      Runtime.Alloc.Block.allocate (nl + vl + 2) none (\b => do
        let MkAddressed e b' = Runtime.Alloc.Block.address b
        Runtime.Memory.copyRaw name e nl
        Runtime.Memory.storeByteAt e nl 0x3D
        Runtime.Memory.copyRaw value (Runtime.Raw.offset e (nl + 1)) vl
        Runtime.Memory.storeByteAt e (nl + 1 + vl) 0
        use b')

||| `unsetenv`: every entry of the name removed and freed, the last entry
||| moved into each one's place; whether the name can be a variable's.
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
          if not ok then Runtime.Ordo.pure False else
            Runtime.Alloc.Blocks.removeAt Runtime.Alloc.Blocks.environment i (\old => do
              Runtime.Alloc.Block.free old
              go)
