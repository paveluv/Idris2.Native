||| The foreign functions of `base`'s `System`, as the runtime implements
||| them: each a flat function of the foreign one's name and type, which the
||| native code generator binds it to (`foreignFunctions`), so that ordinary
||| code calls it through the boundary, which converts its arguments and its
||| result as their types say. A string is the system's text through
||| `Support.Text`, for every encoding.
module Native.Support.Foreign.System

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
-- lint: allow import-unused: the flat check reaches through the environment's bodies, which keep its entries in an array of blocks
import Native.Runtime.Alloc.Blocks
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
-- lint: allow import-unused: the flat check reaches through the allocator's bodies, which use the word operations
import Native.Runtime.Bits
import Native.Runtime.Memory
import Native.Runtime.Ordo as Runtime
import Native.Runtime.Raw as Runtime
-- lint: allow import-unused: the flat check reaches through newPtr's body, which allocates the pointer's object
import Native.Runtime.Space
import Native.Runtime.System
import Native.Support.Environment
-- lint: allow import-unused: the flat check reaches through pointee's body, which reads the pointer's object by its kind
import Native.Support.Obj
import Native.Support.Ptr
import Native.Support.Text
-- lint: allow import-unused: the flat check reaches through newPtr's body, which writes the pointer's header
import Native.Types.Header
-- lint: allow import-unused: the flat check reaches through pointee's body, which reads the pointer's object by its kind
import Native.Types.Kind
import Native.Types.Represents

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

%cg native flat Support.Foreign.System.prim__exit
||| End the process with the status: its low byte is what the parent sees.
export
prim__exit : Int -> PrimIO ()
prim__exit status w = let (Runtime.MkOrdo # ()) = Runtime.System.exit (cast status) Runtime.MkOrdo in MkIORes () w

%cg native flat Support.Foreign.System.prim__getArgCount
||| How many arguments the program has, its name the first, as the system
||| gave them.
export
prim__getArgCount : PrimIO Int
prim__getArgCount w = let (Runtime.MkOrdo # n) = Runtime.Memory.argumentCount Runtime.MkOrdo in MkIORes (cast n) w

%cg native flat Support.Foreign.System.prim__getArg
||| `getArg`: argument `n` of the program, its name argument 0, its text as
||| the system gave it; the empty string for an `n` it has no argument for.
export covering
prim__getArg : Int -> PrimIO (Flat.Uniform String)
prim__getArg n w = let (Runtime.MkOrdo # r) = argOp Runtime.MkOrdo in MkIORes r w
  where
    covering
    argOp : Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform String)
    argOp = do
      count <- Runtime.Memory.argumentCount
      if n < 0 || cast n >= count then Text.emptyText else do
        p <- Runtime.Memory.argumentBytes (cast n)
        Text.zeroEndedText p

%cg native flat Support.Foreign.System.prim__getEnv
||| `getEnv`: the value of the environment's variable of the name
||| (`Support.Environment`), the text after the first entry that holds the
||| name and `=`, copied into a string given as the pointer (`Support.Ptr`),
||| which `base` reads at once; the null pointer for a name no entry has, or
||| no memory to compare it. As the C library's `getenv`, which the other
||| code generators call, the name is compared byte by byte, whatever it
||| holds.
export covering
prim__getEnv : Flat.Uniform String -> PrimIO (Flat.Uniform (Ptr String))
prim__getEnv name w = let (Runtime.MkOrdo # r) = envOp name Runtime.MkOrdo in MkIORes r w
  where
    covering
    envOp : Flat.Uniform String -> Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform (Ptr String))
    envOp name = Text.withText name Ptr.nullPtr (\np, nl => do
      found <- Environment.find np nl
      case found of
        Nothing => Ptr.nullPtr
        Just i => do
          e <- Environment.entryAt i
          v <- Text.zeroEndedText (Runtime.Memory.foreignBytes (e + nl + 1))
          Ptr.stringPtr v)

%cg native flat Support.Foreign.System.prim__getEnvPair
||| `getEnvironment`'s entry `n` of the environment (`Support.Environment`):
||| its text, `NAME=value`, copied into a string given as the pointer
||| (`Support.Ptr`); the null pointer past the last.
export covering
prim__getEnvPair : Int -> PrimIO (Flat.Uniform (Ptr String))
prim__getEnvPair n w = let (Runtime.MkOrdo # r) = pairOp n Runtime.MkOrdo in MkIORes r w
  where
    covering
    pairOp : Int -> Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform (Ptr String))
    pairOp n = if n < 0 then Ptr.nullPtr else do
      e <- Environment.entryAt (cast n)
      if e == 0 then Ptr.nullPtr else do
        v <- Text.zeroEndedText (Runtime.Memory.foreignBytes e)
        Ptr.stringPtr v

%cg native flat Support.Foreign.System.prim__setEnv
||| `setEnv`: the environment's variable of the name set to the value,
||| unless it is set and `overwrite` is 0 (`Support.Environment.set`); 0
||| when it is, -1 when it is not, as the C library's `setenv` answers: for
||| an empty name, one with `=` or a zero byte, or no memory.
export covering
prim__setEnv : Flat.Uniform String -> Flat.Uniform String -> Int -> PrimIO Int
prim__setEnv name value overwrite w = let (Runtime.MkOrdo # r) = setOp name value Runtime.MkOrdo in MkIORes r w
  where
    covering
    setOp : Flat.Uniform String -> Flat.Uniform String -> Runtime.Ordo.Op Runtime.Ordo Int
    setOp name value =
      Text.withText name (Runtime.Ordo.pure (-1)) (\np, nl =>
        Text.withText value (Runtime.Ordo.pure (-1)) (\vp, vl => do
          ok <- Environment.set np nl vp vl (overwrite /= 0)
          Runtime.Ordo.pure (if ok then 0 else -1)))

%cg native flat Support.Foreign.System.prim__unsetEnv
||| `unsetEnv`: every entry of the name removed from the environment
||| (`Support.Environment.unset`); 0, or -1 for a name that cannot be a
||| variable's, as the C library's `unsetenv` answers.
export covering
prim__unsetEnv : Flat.Uniform String -> PrimIO Int
prim__unsetEnv name w = let (Runtime.MkOrdo # r) = unsetOp name Runtime.MkOrdo in MkIORes r w
  where
    covering
    unsetOp : Flat.Uniform String -> Runtime.Ordo.Op Runtime.Ordo Int
    unsetOp name = Text.withText name (Runtime.Ordo.pure (-1)) (\np, nl => do
      ok <- Environment.unset np nl
      Runtime.Ordo.pure (if ok then 0 else -1))
