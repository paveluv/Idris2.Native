||| The foreign functions of the prelude's `Prelude.IO` that no string's
||| layout enters, as the runtime implements them: each a flat function of
||| the foreign one's name and type (`Native.Support.Foreign.System` says
||| how they are bound). Those that read or make a string are the string
||| module's (`prim__putStr` in `Native.Support.String.Utf8`).
module Native.Support.Foreign.Prelude.IO

import Native.Heap
import Native.Runtime.Memory
import Native.Runtime.OS
import Native.Runtime.State
import Native.Support.CodePoint

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

%cg native flat Support.Foreign.Prelude.IO.prim__putChar
||| `putChar`: the character's UTF-8 bytes written to the standard output,
||| from the state's scratch bytes.
export covering
prim__putChar : Char -> PrimIO ()
prim__putChar c w = let (MkHeap # ()) = putOp (cast (ord c)) MkHeap in MkIORes () w
  where
    covering
    putOp : Bits64 -> Heap.Op Heap ()
    putOp cp = do
      b <- Runtime.State.scratchArea
      Runtime.Memory.storeAt b 0 (CodePoint.utf8Word cp)
      Runtime.OS.osWriteAll Runtime.OS.stdout b (CodePoint.utf8Bytes cp)
