||| The system calls of the system tier, on the language's values: a path as a
||| string, the bytes of a buffer, a string's text (`openPath`, `readInto`,
||| `writeFrom`, `writeText`, ...), and the few other places where its
||| ordinary code meets memory by its byte address or a value's
||| representation: the scan of a buffer for a newline (`newlineFrom`), and
||| the handles and the strings given as pointers (`handlePointer`,
||| `stringPointer`).
|||
||| Each is a flat function with an IO type, which ordinary code calls as
||| any other, over the core's OS services and the support tier's door. A
||| call that fails records why as the runtime's last failure, which
||| `getErrno` reads, as the services do.
module Native.System.Call

import Data.Buffer
import Native.Carrier
import Native.Failure
import Native.Field
import Native.Flat.Uniform as Flat
import Native.Mach
import Native.Runtime.Alloc.Block as Runtime.Alloc
import Native.Runtime.ByteAddr as Runtime
import Native.Runtime.Cell
import Native.Runtime.Memory
import Native.Runtime.Ordo as Runtime
import Native.Runtime.OS
import Native.Runtime.PortTy
import Native.Runtime.State
import Native.Support.BufferObj
import Native.Support.Obj
import Native.Support.Ptr
import Native.Support.Text
import Native.Types.Repr

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

%cg native flat System.Call.openPath
||| The file at the path opened with the flags (`Native.OpenFlag`): its
||| handle, the word of all ones if it is not.
export covering
openPath : Flat.Uniform String -> (flags : Bits64) -> IO Bits64
openPath path flags = primIO $ \w => let (Runtime.MkOrdo # h) = op Runtime.MkOrdo in MkIORes h w
  where
    covering
    op : Runtime.Ordo.Op Runtime.Ordo Bits64
    op = Support.Text.withPath path (Runtime.Ordo.pure Runtime.OS.failedWord)
           (\p => Runtime.OS.osOpen p flags)

%cg native flat System.Call.close
||| The handle given back to the system.
export
close : (handle : Bits64) -> IO ()
close h = primIO $ \w => let (Runtime.MkOrdo # _) = Runtime.OS.osClose h Runtime.MkOrdo in
                           MkIORes () w

%cg native flat System.Call.readInto
||| At most `count` bytes read from the handle into the buffer from the
||| offset: how many, 0 at the end, the word of all ones if the read fails.
||| The program ends for bytes outside the buffer.
export
readInto : (handle : Bits64) -> Flat.Uniform Buffer -> (offset, count : Int) -> IO Bits64
readInto h b offset count = primIO $ \w => let (Runtime.MkOrdo # r) =
                                                 op Runtime.MkOrdo in MkIORes r w
  where
    op : Runtime.Ordo.Op Runtime.Ordo Bits64
    op = do
      p <- Support.BufferObj.bytesAt b offset count
      Runtime.OS.osRead h p (cast count)

%cg native flat System.Call.writeFrom
||| `count` bytes of the buffer from the offset written to the handle, all
||| of them; whether they were. The program ends for bytes outside the
||| buffer.
export covering
writeFrom : (handle : Bits64) -> Flat.Uniform Buffer -> (offset, count : Int) -> IO Bool
writeFrom h b offset count = primIO $ \w =>
  let (Runtime.MkOrdo # ok) = op Runtime.MkOrdo in MkIORes ok w
  where
    covering
    op : Runtime.Ordo.Op Runtime.Ordo Bool
    op = do
      p <- Support.BufferObj.bytesAt b offset count
      Runtime.OS.osWriteAll h p (cast count)

%cg native flat System.Call.writeText
||| The string's text written to the handle, all of it; whether it was.
export covering
writeText : (handle : Bits64) -> Flat.Uniform String -> IO Bool
writeText h s = primIO $ \w => let (Runtime.MkOrdo # ok) = op Runtime.MkOrdo in MkIORes ok w
  where
    covering
    op : Runtime.Ordo.Op Runtime.Ordo Bool
    op = Support.Text.withText s (Runtime.Ordo.pure False) (\p, n => Runtime.OS.osWriteAll h p n)

%cg native flat System.Call.fileSize
||| The bytes of the handle's file; the word of all ones if the system does
||| not say.
export
fileSize : (handle : Bits64) -> IO Bits64
fileSize h = primIO $ \w => let (Runtime.MkOrdo # n) = Runtime.OS.osFileSize h Runtime.MkOrdo in
                              MkIORes n w

%cg native flat System.Call.fileTimes
||| The times of the handle's file written into a block of six words
||| `malloc` gave: its last access, modification and change of status,
||| each seconds then nanoseconds (`timesWord`). If the system does not
||| say, the first word is -1, and why is the last failure; the null
||| pointer, which `malloc` gives when there is no memory, is left as it is.
export covering
fileTimes : (handle : Bits64) -> Flat.Uniform AnyPtr -> IO ()
fileTimes h p = primIO $ \w => let (Runtime.MkOrdo # ()) = op Runtime.MkOrdo in MkIORes () w
  where
    covering
    op : Runtime.Ordo.Op Runtime.Ordo ()
    op = do
      target <- Support.Ptr.pointee p
      case target of
        Support.Ptr.Address a =>
          if Runtime.ByteAddr.isNull a then Runtime.Ordo.pure () else do
            ok <- Runtime.OS.osFileTimes h a
            if ok then Runtime.Ordo.pure ()
              else Runtime.Memory.storeAt a 0 0xFFFFFFFFFFFFFFFF
        _ => Runtime.Ordo.pure ()

%cg native flat System.Call.timesWord
||| Word `i` of a block of times `fileTimes` wrote, as an `Int`; -1 for the
||| null pointer, which `malloc` gives when there is no memory, or for a
||| pointer that is no block.
export covering
timesWord : Flat.Uniform AnyPtr -> (i : Bits64) -> IO Int
timesWord p i = primIO $ \w => let (Runtime.MkOrdo # t) = op Runtime.MkOrdo in MkIORes t w
  where
    covering
    op : Runtime.Ordo.Op Runtime.Ordo Int
    op = do
      target <- Support.Ptr.pointee p
      case target of
        Support.Ptr.Address a =>
          if Runtime.ByteAddr.isNull a then Runtime.Ordo.pure (-1) else do
            t <- Runtime.Memory.loadAt a (8 * i)
            Runtime.Ordo.pure (cast t)
        _ => Runtime.Ordo.pure (-1)

%cg native flat System.Call.isTerminal
||| Whether the handle is a terminal's.
export
isTerminal : (handle : Bits64) -> IO Bool
isTerminal h = primIO $ \w => let (Runtime.MkOrdo # t) = Runtime.OS.osIsTerminal h Runtime.MkOrdo in
                                MkIORes t w

%cg native flat System.Call.removePath
||| The file at the path removed, or the empty directory, as the C
||| library's `remove`; whether it was.
export covering
removePath : Flat.Uniform String -> IO Bool
removePath path = primIO $ \w => let (Runtime.MkOrdo # ok) = op Runtime.MkOrdo in MkIORes ok w
  where
    covering
    op : Runtime.Ordo.Op Runtime.Ordo Bool
    op = Support.Text.withPath path (Runtime.Ordo.pure False) (\p => do
      ok <- Runtime.OS.osRemoveFile p
      if ok then Runtime.Ordo.pure True else do
        why <- Runtime.State.get "lastFailure"
        if why /= Failure.code Failure.IsADirectory then Runtime.Ordo.pure False else do
          Runtime.OS.osRemoveDirectory p)

%cg native flat System.Call.readEntry
||| The next entry's name of the directory of the handle, `.` and `..`
||| among them; the empty string when there are no more, or if the read
||| fails, which then records why as the last failure.
export covering
readEntry : (handle : Bits64) -> IO (Flat.Uniform String)
readEntry h = primIO $ \w => let (Runtime.MkOrdo # s) = op Runtime.MkOrdo in MkIORes s w
  where
    ||| The bytes of an entry's name, its zero byte one: enough on every
    ||| platform (`Service.ReadEntry`).
    nameBytes : Bits64
    nameBytes = 256

    covering
    op : Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform String)
    op = Runtime.Alloc.Block.allocate nameBytes Support.Text.emptyText (\b => do
      let Runtime.Alloc.Block.MkAddressed q b' = Runtime.Alloc.Block.address b
      n <- Runtime.OS.osReadEntry h q nameBytes
      s <- if n == 0 || n == Runtime.OS.failedWord then Support.Text.emptyText
        else Support.Text.ofText q n
      Runtime.Alloc.Block.free b'
      Runtime.Ordo.pure s)

%cg native flat System.Call.clearFailure
||| The runtime's last failure cleared, so that one a call records is told
||| from none, as the C library's callers clear `errno`.
export
clearFailure : IO ()
clearFailure = primIO $ \w =>
  let (Runtime.MkOrdo # ()) = Runtime.State.set "lastFailure" 0 Runtime.MkOrdo in
    MkIORes () w

%cg native flat System.Call.recordFailure
||| The reason, by its code (`Native.Failure`), recorded as the runtime's
||| last failure, for a call the system tier refuses itself.
export
recordFailure : (code : Bits64) -> IO ()
recordFailure c = primIO $ \w =>
  let (Runtime.MkOrdo # ()) = Runtime.State.set "lastFailure" c Runtime.MkOrdo in
    MkIORes () w

%cg native flat System.Call.newlineFrom
||| The offset of the first newline in the buffer from `from`, or `to` if
||| there is none before it. The program ends for bytes outside the buffer.
export covering
newlineFrom : Flat.Uniform Buffer -> (from, to : Int) -> IO Int
newlineFrom b from to = primIO $ \w => let (Runtime.MkOrdo # i) = op Runtime.MkOrdo in MkIORes i w
  where
    -- the first newline from byte `i` of the `n` at the address
    covering
    scan : Runtime.ByteAddr -> (i, n : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bits64
    scan p i n = if i >= n then Runtime.Ordo.pure n else do
      c <- Runtime.Memory.loadByteAt p i
      if c == 10 then Runtime.Ordo.pure i else scan p (i + 1) n

    covering
    op : Runtime.Ordo.Op Runtime.Ordo Int
    op = if to <= from then Runtime.Ordo.pure to else do
      p <- Support.BufferObj.bytesAt b from (to - from)
      i <- scan p 0 (cast (to - from))
      Runtime.Ordo.pure (from + cast i)

%cg native flat System.Call.handlePointer
||| The pointer a handle is given as (`Types.Repr.Handles`).
export
handlePointer : (number : Int) -> Flat.Uniform AnyPtr
handlePointer n = let (Runtime.MkOrdo # p) = Support.Obj.handleValue (cast n) Runtime.MkOrdo in p

%cg native flat System.Call.pointerHandle
||| The handle a pointer is, if it is one; -1 if it is not.
export
pointerHandle : Flat.Uniform AnyPtr -> Int
pointerHandle p = let (Runtime.MkOrdo # h) = Support.Obj.valueHandle p Runtime.MkOrdo in
                    maybe (-1) cast h

%cg native flat System.Call.stringPointer
||| A string given as a pointer to its text (`Support.Ptr`), which `base`
||| reads by `getString`.
export
stringPointer : Flat.Uniform String -> Flat.Uniform (Ptr String)
stringPointer s = let (Runtime.MkOrdo # p) = Support.Ptr.stringPtr s Runtime.MkOrdo in p

%cg native flat System.Call.nullString
||| The null pointer, given for no string.
export
nullString : Flat.Uniform (Ptr String)
nullString = let (Runtime.MkOrdo # p) = Support.Ptr.nullPtr Runtime.MkOrdo in p

%cg native flat System.Call.nullPointer
||| The null pointer, given for no file.
export
nullPointer : Flat.Uniform AnyPtr
nullPointer = let (Runtime.MkOrdo # p) = Support.Ptr.nullPtr Runtime.MkOrdo in p
