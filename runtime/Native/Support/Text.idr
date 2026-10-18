||| Strings as the system's text (`withText`, `withPath`, `ofText`,
||| `zeroEndedText`): the bytes the system takes and gives, UTF-8 on every
||| platform targeted, whatever the program's strings are.
|||
||| The program's string encoding's module knows how a string's text
||| becomes the system's bytes and back; this module asks it, through an
||| extern of each such string routine (`Types.StringRoutine`'s `TextBytes`,
||| `TextAddress`, `CopyText`, `OfText`), which the native code generator
||| binds to the encoding's function, as it binds an OS service's to the
||| platform's. So the runtime's code that speaks to the system (the
||| environment, the directories, the console) is written once, here and
||| over these, for every encoding.
module Native.Support.Text

-- lint: allow public-import: an extern's type, written by its port, reduces only
-- where the port and its reading are visible, so they are wherever this
-- module is, whose wrappers the flat translation unfolds into its importers
import public Native.Port
import public Native.Runtime.PortTy
import public Native.Types.StringRoutine

import Native.Failure
import Native.Flat.Uniform as Flat
import Native.HeapObj.Shape as HeapObj
import Native.Runtime.Alloc.Block
import Native.Runtime.Memory
import Native.Runtime.Ordo as Runtime
import Native.Runtime.Raw as Runtime
import Native.Runtime.State

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

%extern string__textBytes : Runtime.PortTy.ExternTy (Types.StringRoutine.port Types.StringRoutine.TextBytes)
%extern string__textAddress : Runtime.PortTy.ExternTy (Types.StringRoutine.port Types.StringRoutine.TextAddress)
%extern string__copyText : Runtime.PortTy.ExternTy (Types.StringRoutine.port Types.StringRoutine.CopyText)
%extern string__ofText : Runtime.PortTy.ExternTy (Types.StringRoutine.port Types.StringRoutine.OfText)

||| A new string of the `len` bytes of the system's text at the address.
export %inline
ofText : (bytes : Runtime.Raw) -> (len : Bits64) -> Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform String)
ofText = string__ofText

||| The empty string.
export %inline
emptyText : Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform String)
emptyText = string__ofText Runtime.Raw.null 0

||| The string of the system's text at the address up to the zero byte
||| that ends it: an argument, an environment entry, a path, as the system
||| gave it.
export covering
zeroEndedText : Runtime.Raw -> Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform String)
zeroEndedText p = do
  len <- zeroAt 0
  string__ofText p len
  where
    -- the bytes up to the zero byte that ends them
    covering
    zeroAt : Bits64 -> Runtime.Ordo.Op Runtime.Ordo Bits64
    zeroAt i = do
      b <- Runtime.Memory.loadByteAt p i
      if b == 0 then Runtime.Ordo.pure i else zeroAt (i + 1)

||| `use` of a string's text as the system's bytes, at an address and so
||| many: the string's own where the encoding holds its text so, else a copy
||| in a block outside the heap, freed after; `none`, with the runtime's last
||| failure that there is no memory, if there is none for the copy.
export %inline covering
withText : Flat.Uniform String -> (none : Runtime.Ordo.Op Runtime.Ordo a) ->
           (use : Runtime.Raw -> Bits64 -> Runtime.Ordo.Op Runtime.Ordo a) -> Runtime.Ordo.Op Runtime.Ordo a
withText s none use = do
  n <- string__textBytes s
  own <- string__textAddress s
  if not (Runtime.Raw.isNull own) then use own n else
    Runtime.Alloc.Block.allocate n
      (do Runtime.State.setState Runtime.State.lastFailure (Failure.code Failure.NoMemory)
          none)
      (\b => do
        let MkAddressed p b' = Runtime.Alloc.Block.address b
        string__copyText s p
        r <- use p n
        Runtime.Alloc.Block.free b'
        Runtime.Ordo.pure r)

||| `use` of a string as a path, as the system takes one: its text as the
||| system's bytes and a zero byte after them, in a block outside the heap,
||| freed after; `none`, with the runtime's last failure that there is no
||| memory, if there is none for the block. The system reads a path up to
||| its first zero byte, so one inside the string ends it there, as the C
||| library's callers find.
export %inline covering
withPath : Flat.Uniform String -> (none : Runtime.Ordo.Op Runtime.Ordo a) ->
           (use : Runtime.Raw -> Runtime.Ordo.Op Runtime.Ordo a) -> Runtime.Ordo.Op Runtime.Ordo a
withPath s none use = do
  n <- string__textBytes s
  Runtime.Alloc.Block.allocate (n + 1)
    (do Runtime.State.setState Runtime.State.lastFailure (Failure.code Failure.NoMemory)
        none)
    (\b => do
      let MkAddressed p b' = Runtime.Alloc.Block.address b
      string__copyText s p
      Runtime.Memory.storeByteAt p n 0
      r <- use p
      Runtime.Alloc.Block.free b'
      Runtime.Ordo.pure r)
