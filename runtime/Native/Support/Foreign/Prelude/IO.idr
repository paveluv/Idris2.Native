||| The foreign functions of the prelude's `Prelude.IO`, as the runtime
||| implements them: each a flat function of the foreign one's name and type
||| (`Native.Support.Foreign.System` says how they are bound). A string is
||| the system's text through `Support.Text`, for every encoding.
module Native.Support.Foreign.Prelude.IO

-- lint: allow import-unused: the flat check reaches through withText's body, which records the failure of no memory
import Native.Failure
import Native.Flat.Uniform as Flat
-- lint: allow import-unused: the flat check reaches through pointee's body, which reads the pointer's object by its kind
import Native.HeapObj.Shape as HeapObj
-- lint: allow import-unused: the flat check reaches through withText's body, which copies a string into a block outside the heap
import Native.Runtime.Alloc.Allocator
-- lint: allow import-unused: the flat check reaches through withText's body, which copies a string into a block outside the heap
import Native.Runtime.Alloc.Arena
-- lint: allow import-unused: the flat check reaches through withText's body, which copies a string into a block outside the heap
import Native.Runtime.Alloc.Block
-- lint: allow import-unused: the flat check reaches through withText's body, which copies a string into a block outside the heap
import Native.Runtime.Alloc.Chunks
-- lint: allow import-unused: the flat check reaches through withText's body, which copies a string into a block outside the heap
import Native.Runtime.Alloc.Config
-- lint: allow import-unused: the flat check reaches through withText's body, which copies a string into a block outside the heap
import Native.Runtime.Alloc.Pages
-- lint: allow import-unused: the flat check reaches through withText's body, which copies a string into a block outside the heap
import Native.Runtime.Alloc.SizeClasses
-- lint: allow import-unused: the flat check reaches through withText's body, which copies a string into a block outside the heap
import Native.Runtime.Alloc.System
import Native.Runtime.Memory
import Native.Runtime.Ordo as Runtime
import Native.Runtime.OS
import Native.Runtime.Raw as Runtime
import Native.Runtime.State
import Native.Support.CodePoint
import Native.Support.Obj
import Native.Support.Ptr
import Native.Support.Text
import Native.Types.Kind
import Native.Types.Represents

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

%cg native flat Support.Foreign.Prelude.IO.prim__putChar
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
      Runtime.Memory.storeAt b 0 (CodePoint.utf8Word cp)
      Runtime.OS.osWriteAll Runtime.OS.stdout b (CodePoint.utf8Bytes cp)

%cg native flat Support.Foreign.Prelude.IO.prim__putStr
||| `putStr`: the string's text written to the standard output, all of it.
||| Nothing is buffered, so nothing waits to be flushed.
export covering
prim__putStr : Flat.Uniform String -> PrimIO ()
prim__putStr str w = let (Runtime.MkOrdo # ()) = putOp str Runtime.MkOrdo in MkIORes () w
  where
    covering
    putOp : Flat.Uniform String -> Runtime.Ordo.Op Runtime.Ordo ()
    putOp str = Text.withText str (Runtime.Ordo.pure ()) (\p, n => Runtime.OS.osWriteAll Runtime.OS.stdout p n)

%cg native flat Support.Foreign.Prelude.IO.prim__getString
||| `getString`: the string a pointer is, if it is one of the heap
||| (`Support.Ptr`), itself; else the zero-ended text it points to, copied;
||| the empty string for the null pointer, which the C library would read
||| through.
export covering
prim__getString : Flat.Uniform (Ptr String) -> Flat.Uniform String
prim__getString p = let (Runtime.MkOrdo # r) = getOp Runtime.MkOrdo in r
  where
    covering
    getOp : Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform String)
    getOp = do
      target <- Ptr.pointee p
      case target of
        HeapString s => Obj.objectValue s
        Address a => if Runtime.Raw.isNull a then Text.emptyText else Text.zeroEndedText a
