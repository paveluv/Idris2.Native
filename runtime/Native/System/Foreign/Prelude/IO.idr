||| The foreign functions of the prelude's `Prelude.IO` that write to the
||| standard output or read the standard input, as the system tier
||| implements them: each a function of the foreign one's name and type
||| (`Native.System` says how they are bound). A string is the system's text
||| through `Support.Text`, for every encoding.
module Native.System.Foreign.Prelude.IO

import Native.Flat.Uniform as Flat
import Native.Runtime.ByteAddr as Runtime
import Native.Runtime.Memory
import Native.Runtime.Ordo as Runtime
import Native.Runtime.OS
import Native.Runtime.State
import Native.Support.CodePoint
import Native.Support.Text
import Native.System.File

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

%cg native flat System.Foreign.Prelude.IO.prim__putChar
||| `putChar`: the character's UTF-8 bytes written to the standard output,
||| from the state's scratch bytes.
export covering
prim__putChar : Char -> PrimIO ()
prim__putChar c w = let (Runtime.MkOrdo # ()) = putOp (cast (ord c)) Runtime.MkOrdo in MkIORes () w
  where
    covering
    putOp : Bits64 -> Runtime.Ordo.Op Runtime.Ordo ()
    putOp cp = do
      b <- Runtime.State.scratchArea
      Runtime.Memory.storeAt b 0 (Support.CodePoint.utf8Word cp)
      _ <- Runtime.OS.osWriteAll Runtime.OS.stdout b (Support.CodePoint.utf8Bytes cp)
      Runtime.Ordo.pure ()

%cg native flat System.Foreign.Prelude.IO.prim__putStr
||| `putStr`: the string's text written to the standard output, all of it.
||| Nothing is buffered, so nothing waits to be flushed.
export covering
prim__putStr : Flat.Uniform String -> PrimIO ()
prim__putStr str w = let (Runtime.MkOrdo # ()) = putOp str Runtime.MkOrdo in MkIORes () w
  where
    covering
    putOp : Flat.Uniform String -> Runtime.Ordo.Op Runtime.Ordo ()
    putOp str =
      Support.Text.withText str (Runtime.Ordo.pure ())
        (\p, n => do
          _ <- Runtime.OS.osWriteAll Runtime.OS.stdout p n
          Runtime.Ordo.pure ())

||| `getLine`: the standard input's text through the next newline, without
||| it, or to its end; the empty string there, as the Chez backend's
||| `get-line` gives.
export covering
prim__getStr : PrimIO String
prim__getStr = toPrim $ File.withFile (File.standard 0) "" (\_, f => File.readLine False f)
