||| The inline externs (`InlineExtern`): what the lowering provides to
||| fragment code.
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Native.Codegen.Linkage.Routine` says what it is).
module Native.Codegen.Linkage.InlineExtern

import Native.Codegen.Linkage.RuntimeModule

import Core.Name
import Data.Fin
import Data.List
import Native.Area
import Native.Codegen.IRCommon.Intrinsic as IRCommon
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.HeapObj.Enc as HeapObj
import Native.HeapObj.Kind as HeapObj

%default total

||| The inline externs: the `%extern` primitives of the runtime library that
||| are instructions, never calls, what the runtime is written with. Each
||| takes words and the token, which has no register, last, and returns the
||| token with its value, so that its effect is ordered among the others by
||| data dependence. A memory access is at a base address plus a byte
||| offset; a narrow load extends the bits with zeros.
public export
data InlineExtern
  = ||| An intrinsic, on words: a pointer it takes or gives is the pointer's
    ||| word.
    Machine IRCommon.Intrinsic
  | ||| Load a word.
    Load64
  | ||| Load 8, 16 or 32 bits.
    LoadNarrow IRCommon.Op.SubWord
  | ||| Store a word.
    Store64
  | ||| Store a word's low 8, 16 or 32 bits.
    StoreNarrow IRCommon.Op.SubWord
  | ||| The pointer tag of the program's encoding: what a pointer word is
    ||| beyond the object's address.
    PointerTag
  | ||| The address of a per-thread area.
    AreaAddress Area
  | ||| The pointer word of a uniform value known to be an object of the kind.
    ObjectWord HeapObj.Kind
  | ||| The uniform value of a pointer word to an object of the kind.
    WordObject HeapObj.Kind

||| An inline extern as the runtime library declares it: the registers of
||| its arguments, the token among them taking none, and of its result.
public export
record InlineExternSig (0 enc : HeapObj.Enc) where
  constructor MkInlineExternSig
  name : Name
  extern : InlineExtern
  params : List (IRCommon.Ty enc)
  results : List (IRCommon.Ty enc)

||| The inline externs, with their signatures.
export
inlineExterns : {0 enc : HeapObj.Enc} -> List (InlineExternSig enc)
inlineExterns =
  [ machine "OS.Syscall" "prim__syscall6" (IRCommon.Intrinsic.Syscall 6)
  , memory "prim__load64" Load64 [IRCommon.Ty.W64, IRCommon.Ty.W64] [IRCommon.Ty.W64]
  , memory "prim__load32" (LoadNarrow IRCommon.Op.Sub32) [IRCommon.Ty.W64, IRCommon.Ty.W64] [IRCommon.Ty.W64]
  , memory "prim__load16" (LoadNarrow IRCommon.Op.Sub16) [IRCommon.Ty.W64, IRCommon.Ty.W64] [IRCommon.Ty.W64]
  , memory "prim__load8" (LoadNarrow IRCommon.Op.Sub8) [IRCommon.Ty.W64, IRCommon.Ty.W64] [IRCommon.Ty.W64]
  , memory "prim__store64" Store64 [IRCommon.Ty.W64, IRCommon.Ty.W64, IRCommon.Ty.W64] []
  , memory "prim__store32" (StoreNarrow IRCommon.Op.Sub32) [IRCommon.Ty.W64, IRCommon.Ty.W64, IRCommon.Ty.W64] []
  , memory "prim__store16" (StoreNarrow IRCommon.Op.Sub16) [IRCommon.Ty.W64, IRCommon.Ty.W64, IRCommon.Ty.W64] []
  , memory "prim__store8" (StoreNarrow IRCommon.Op.Sub8) [IRCommon.Ty.W64, IRCommon.Ty.W64, IRCommon.Ty.W64] []
  , machine "Memory" "prim__getHp" IRCommon.Intrinsic.GetHp
  , machine "Memory" "prim__setHp" IRCommon.Intrinsic.SetHp
  , machine "Memory" "prim__getHpLim" IRCommon.Intrinsic.GetHpLim
  , machine "Memory" "prim__setHpLim" IRCommon.Intrinsic.SetHpLim
  , machine "Memory" "prim__getK" IRCommon.Intrinsic.GetK
  , machine "Memory" "prim__setK" IRCommon.Intrinsic.SetK
  , memory "prim__pointerTag" PointerTag [] [IRCommon.Ty.W64]
  , memory "prim__stackLimitArea" (AreaAddress Area.STACK_LIMIT) [] [IRCommon.Ty.W64]
  , memory "prim__argvArea" (AreaAddress Area.ARGV) [] [IRCommon.Ty.W64]
  , memory "prim__rootsArea" (AreaAddress Area.ROOTS) [] [IRCommon.Ty.W64]
  , memory "prim__nrootsArea" (AreaAddress Area.NROOTS) [] [IRCommon.Ty.W64]
  , memory "prim__runtimeArea" (AreaAddress Area.RUNTIME) [] [IRCommon.Ty.W64]
  , memory "prim__stringWord" (ObjectWord HeapObj.Kind.STRING) [IRCommon.Ty.Val] [IRCommon.Ty.W64]
  , memory "prim__wordString" (WordObject HeapObj.Kind.STRING) [IRCommon.Ty.W64] [IRCommon.Ty.Val]
  , memory "prim__conWord" (ObjectWord HeapObj.Kind.CON) [IRCommon.Ty.Val] [IRCommon.Ty.W64]
  , memory "prim__wordCon" (WordObject HeapObj.Kind.CON) [IRCommon.Ty.W64] [IRCommon.Ty.Val] ]
  where
    sig : String -> String -> InlineExtern -> List (IRCommon.Ty enc) -> List (IRCommon.Ty enc) -> InlineExternSig enc
    sig m n = MkInlineExternSig (NS (RuntimeModule.runtimeModule m) (UN (Basic n)))

    memory : String -> InlineExtern -> List (IRCommon.Ty enc) -> List (IRCommon.Ty enc) -> InlineExternSig enc
    memory = sig "Memory"

    word : IRCommon.Ty enc -> IRCommon.Ty enc
    word (IRCommon.Ty.PtrTo _) = IRCommon.Ty.W64
    word t = t

    -- an intrinsic's own signature, a pointer in it a word
    machine : String -> String -> IRCommon.Intrinsic -> InlineExternSig enc
    machine ns n i =
      sig ns n (Machine i) (map word (IRCommon.Intrinsic.params i)) (map word (IRCommon.Intrinsic.results i))

||| The inline extern a primitive of the runtime library is, by its name.
export
inlineExternOf : {0 enc : HeapObj.Enc} -> Name -> Maybe InlineExtern
inlineExternOf n = (.extern) <$> find (\i => i.name == n) (inlineExterns {enc})
