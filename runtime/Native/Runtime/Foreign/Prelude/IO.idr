||| The foreign functions of the prelude's `Prelude.IO` that no string's
||| layout enters, as the runtime implements them: each a flat function of
||| the foreign one's name and type (`Native.Runtime.Foreign.System` says
||| how they are bound). Those that read or make a string are the string
||| module's (`prim__putStr` in `Native.Runtime.String.Utf8`).
module Native.Runtime.Foreign.Prelude.IO

import Native.Heap
import Native.HeapObj.Kind
import Native.Runtime.CodePoint
import Native.Runtime.Memory
import Native.Runtime.OS
import Native.Runtime.State

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

%cg native flat Runtime.Foreign.Prelude.IO.prim__putChar
||| `putChar`: the character's UTF-8 bytes written to the standard output,
||| from the state's scratch bytes.
export covering
prim__putChar : Char -> PrimIO ()
prim__putChar c w = let (MkHeap # ()) = putOp (cast (ord c)) MkHeap in MkIORes () w
  where
    covering
    putOp : Bits64 -> Heap.Op Heap ()
    putOp cp = do
      b <- State.scratchArea {k = HeapObj.Kind.BUFFER}
      CodePoint.encodeUtf8 b 0 cp
      OS.osWriteAll OS.stdout (Memory.toWord b) (CodePoint.utf8Bytes cp)
