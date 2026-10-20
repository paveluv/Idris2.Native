||| The foreign functions of `base`'s `System`, as the system tier
||| implements them: the process's end, its arguments and its environment,
||| each a flat function of the foreign one's name and type (`Native.System`
||| says how they are bound). A string is the system's text through
||| `Support.Text`, for every encoding.
module Native.System.Foreign.System

import Native.Flat.Uniform as Flat
import Native.Runtime.ByteAddr as Runtime
import Native.Runtime.Memory
import Native.Runtime.Ordo as Runtime
import Native.Runtime.System
import Native.Support.Ptr
import Native.Support.Text
import Native.System.Environment
import Native.Types.Represents

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

%cg native flat System.Foreign.System.prim__exit
||| End the process with the status: its low byte is what the parent sees.
export
prim__exit : Int -> PrimIO ()
prim__exit status w = let (Runtime.MkOrdo # ()) =
                            Runtime.System.exit (cast status) Runtime.MkOrdo in MkIORes () w

%cg native flat System.Foreign.System.prim__getArgCount
||| How many arguments the program has, its name the first, as the system
||| gave them.
export
prim__getArgCount : PrimIO Int
prim__getArgCount w = let (Runtime.MkOrdo # n) =
                            Runtime.Memory.argumentCount Runtime.MkOrdo in MkIORes (cast n) w

%cg native flat System.Foreign.System.prim__getArg
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
      if n < 0 || cast n >= count then Support.Text.emptyText else do
        p <- Runtime.Memory.argumentBytes (cast n)
        Support.Text.zeroEndedText p

%cg native flat System.Foreign.System.prim__getEnv
||| `getEnv`: the value of the environment's variable of the name
||| (`System.Environment`), the text after the first entry that holds the
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
    envOp name = Support.Text.withText name Support.Ptr.nullPtr (\np, nl => do
      found <- Environment.find np nl
      case found of
        Nothing => Support.Ptr.nullPtr
        Just i => do
          e <- Environment.entryAt i
          v <- Support.Text.zeroEndedText (Runtime.Memory.foreignBytes (e + nl + 1))
          Support.Ptr.stringPtr v)

%cg native flat System.Foreign.System.prim__getEnvPair
||| `getEnvironment`'s entry `n` of the environment (`System.Environment`):
||| its text, `NAME=value`, copied into a string given as the pointer
||| (`Support.Ptr`); the null pointer past the last.
export covering
prim__getEnvPair : Int -> PrimIO (Flat.Uniform (Ptr String))
prim__getEnvPair n w = let (Runtime.MkOrdo # r) = pairOp n Runtime.MkOrdo in MkIORes r w
  where
    covering
    pairOp : Int -> Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform (Ptr String))
    pairOp n = if n < 0 then Support.Ptr.nullPtr else do
      e <- Environment.entryAt (cast n)
      if e == 0 then Support.Ptr.nullPtr else do
        v <- Support.Text.zeroEndedText (Runtime.Memory.foreignBytes e)
        Support.Ptr.stringPtr v

%cg native flat System.Foreign.System.prim__setEnv
||| `setEnv`: the environment's variable of the name set to the value,
||| unless it is set and `overwrite` is 0 (`System.Environment.set`); 0
||| when it is, -1 when it is not, as the C library's `setenv` answers: for
||| an empty name, one with `=` or a zero byte, or no memory.
export covering
prim__setEnv : Flat.Uniform String -> Flat.Uniform String -> Int -> PrimIO Int
prim__setEnv name value overwrite w = let (Runtime.MkOrdo # r) =
                                            setOp name value Runtime.MkOrdo in MkIORes r w
  where
    covering
    setOp : Flat.Uniform String -> Flat.Uniform String -> Runtime.Ordo.Op Runtime.Ordo Int
    setOp name value =
      Support.Text.withText name (Runtime.Ordo.pure (-1)) (\np, nl =>
        Support.Text.withText value (Runtime.Ordo.pure (-1)) (\vp, vl => do
          ok <- Environment.set np nl vp vl (overwrite /= 0)
          Runtime.Ordo.pure (if ok then 0 else -1)))

%cg native flat System.Foreign.System.prim__unsetEnv
||| `unsetEnv`: every entry of the name removed from the environment
||| (`System.Environment.unset`); 0, or -1 for a name that cannot be a
||| variable's, as the C library's `unsetenv` answers.
export covering
prim__unsetEnv : Flat.Uniform String -> PrimIO Int
prim__unsetEnv name w = let (Runtime.MkOrdo # r) = unsetOp name Runtime.MkOrdo in MkIORes r w
  where
    covering
    unsetOp : Flat.Uniform String -> Runtime.Ordo.Op Runtime.Ordo Int
    unsetOp name = Support.Text.withText name (Runtime.Ordo.pure (-1)) (\np, nl => do
      ok <- Environment.unset np nl
      Runtime.Ordo.pure (if ok then 0 else -1))
