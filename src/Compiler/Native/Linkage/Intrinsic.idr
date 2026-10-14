||| The intrinsics (`Intrinsic`): what the lowering provides to fragment
||| code.
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Compiler.Native.Linkage.Routine` says what it is).
module Compiler.Native.Linkage.Intrinsic

import Compiler.Native.HeapObject.Enc
import Compiler.Native.HeapObject.Kind
import Compiler.Native.IRCommon.Area
import Compiler.Native.IRCommon.Operators.SubWord
import Compiler.Native.IRCommon.Ty
import Core.Name
import Data.List

%default total

||| The intrinsics: the `%extern` primitives of the runtime library that are
||| instructions, never calls, what the runtime is written with. Each takes
||| words and the token, which has no register, last, and returns the token
||| with its value, so that its effect is ordered among the others by data
||| dependence. A memory access is at a base address plus a byte offset; a
||| narrow load extends the bits with zeros.
public export
data Intrinsic
  = ||| A system call: its number and six arguments, then its result.
    Syscall6
  | ||| Load a word.
    Load64
  | ||| Load 8, 16 or 32 bits.
    LoadNarrow SubWord
  | ||| Store a word.
    Store64
  | ||| Store a word's low 8, 16 or 32 bits.
    StoreNarrow SubWord
  | ||| The allocation pointer.
    GetHp
  | ||| Set the allocation pointer.
    SetHp
  | ||| The allocation limit.
    GetHpLim
  | ||| Set the allocation limit.
    SetHpLim
  | ||| The current continuation, as the pointer word it is.
    GetK
  | ||| Set the current continuation from a pointer word.
    SetK
  | ||| The pointer tag of the program's encoding: what a pointer word is
    ||| beyond the object's address.
    PointerTag
  | ||| The address of a per-thread area.
    AreaAddress Area
  | ||| The pointer word of a uniform value known to be an object of the kind.
    ObjectWord Kind
  | ||| The uniform value of a pointer word to an object of the kind.
    WordObject Kind

||| An intrinsic as the runtime library declares it: the registers of its
||| arguments, the token among them taking none, and of its result.
public export
record IntrinsicSig (0 enc : Enc) where
  constructor MkIntrinsicSig
  name : Name
  intrinsic : Intrinsic
  params : List (Ty enc)
  results : List (Ty enc)

||| The intrinsics, with their signatures.
export
intrinsics : {0 enc : Enc} -> List (IntrinsicSig enc)
intrinsics =
  [ MkIntrinsicSig (NS (mkNamespace "Runtime.OS.Syscall") (UN (Basic "prim__syscall6"))) Syscall6 (replicate 7 W64) [W64]
  , memory "prim__load64" Load64 [W64, W64] [W64]
  , memory "prim__load32" (LoadNarrow Sub32) [W64, W64] [W64]
  , memory "prim__load16" (LoadNarrow Sub16) [W64, W64] [W64]
  , memory "prim__load8" (LoadNarrow Sub8) [W64, W64] [W64]
  , memory "prim__store64" Store64 [W64, W64, W64] []
  , memory "prim__store32" (StoreNarrow Sub32) [W64, W64, W64] []
  , memory "prim__store16" (StoreNarrow Sub16) [W64, W64, W64] []
  , memory "prim__store8" (StoreNarrow Sub8) [W64, W64, W64] []
  , memory "prim__getHp" GetHp [] [W64]
  , memory "prim__setHp" SetHp [W64] []
  , memory "prim__getHpLim" GetHpLim [] [W64]
  , memory "prim__setHpLim" SetHpLim [W64] []
  , memory "prim__getK" GetK [] [W64]
  , memory "prim__setK" SetK [W64] []
  , memory "prim__pointerTag" PointerTag [] [W64]
  , memory "prim__stackLimitArea" (AreaAddress STACK_LIMIT) [] [W64]
  , memory "prim__argvArea" (AreaAddress ARGV) [] [W64]
  , memory "prim__rootsArea" (AreaAddress ROOTS) [] [W64]
  , memory "prim__nrootsArea" (AreaAddress NROOTS) [] [W64]
  , memory "prim__runtimeArea" (AreaAddress RUNTIME) [] [W64]
  , memory "prim__stringWord" (ObjectWord STRING) [Val] [W64]
  , memory "prim__wordString" (WordObject STRING) [W64] [Val]
  , memory "prim__conWord" (ObjectWord CON) [Val] [W64]
  , memory "prim__wordCon" (WordObject CON) [W64] [Val] ]
  where
    memory : String -> Intrinsic -> List (Ty enc) -> List (Ty enc) -> IntrinsicSig enc
    memory n = MkIntrinsicSig (NS (mkNamespace "Runtime.Memory") (UN (Basic n)))

||| The intrinsic a primitive of the runtime library is, by its name.
export
intrinsicOf : {0 enc : Enc} -> Name -> Maybe Intrinsic
intrinsicOf n = (.intrinsic) <$> find (\i => i.name == n) (intrinsics {enc})
