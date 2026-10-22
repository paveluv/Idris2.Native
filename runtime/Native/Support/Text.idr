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

import Native.Failure
import Native.Flat.Uniform as Flat
import Native.Runtime.Alloc.Block as Runtime.Alloc
import Native.Runtime.ByteAddr as Runtime
import Native.Runtime.Cell
import Native.Runtime.Memory
import Native.Runtime.Ordo as Runtime
import Native.Runtime.PortTy as Runtime
import Native.Runtime.State
import Native.Types.StringRoutine

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

%extern string__textBytes : Runtime.PortTy
                            (Types.StringRoutine.port Types.StringRoutine.TextBytes)
%extern string__textAddress : Runtime.PortTy
                              (Types.StringRoutine.port Types.StringRoutine.TextAddress)
%extern string__copyText : Runtime.PortTy
                           (Types.StringRoutine.port Types.StringRoutine.CopyText)
%extern string__ofText : Runtime.PortTy
                         (Types.StringRoutine.port Types.StringRoutine.OfText)

||| The bytes of a string's text as the system's.
export %inline
textBytes : Flat.Uniform String -> Runtime.Ordo.Op Runtime.Ordo Bits64
textBytes = string__textBytes

||| A new string of the `len` bytes of the system's text at the address.
export %inline
ofText : (bytes : Runtime.ByteAddr) -> (len : Bits64) ->
         Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform String)
ofText = string__ofText

||| The empty string.
export %inline
emptyText : Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform String)
emptyText = string__ofText Runtime.ByteAddr.null 0

||| The string of the system's text at the address up to the zero byte
||| that ends it: an argument, an environment entry, a path, as the system
||| gave it.
export covering
zeroEndedText : Runtime.ByteAddr -> Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform String)
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
           (use : Runtime.ByteAddr -> Bits64 -> Runtime.Ordo.Op Runtime.Ordo a) ->
           Runtime.Ordo.Op Runtime.Ordo a
withText s none use = do
  n <- string__textBytes s
  own <- string__textAddress s
  if not (Runtime.ByteAddr.isNull own) then use own n else
    Runtime.Alloc.Block.allocate n
      (do Runtime.State.setState Runtime.State.lastFailure (Failure.code Failure.NoMemory)
          none)
      (\b => do
        let Runtime.Alloc.Block.MkAddressed p b' = Runtime.Alloc.Block.address b
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
           (use : Runtime.ByteAddr -> Runtime.Ordo.Op Runtime.Ordo a) ->
           Runtime.Ordo.Op Runtime.Ordo a
withPath s none use = do
  n <- string__textBytes s
  Runtime.Alloc.Block.allocate (n + 1)
    (do Runtime.State.setState Runtime.State.lastFailure (Failure.code Failure.NoMemory)
        none)
    (\b => do
      let Runtime.Alloc.Block.MkAddressed p b' = Runtime.Alloc.Block.address b
      string__copyText s p
      Runtime.Memory.storeByteAt p n 0
      r <- use p
      Runtime.Alloc.Block.free b'
      Runtime.Ordo.pure r)
