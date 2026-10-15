||| The inline externs (`InlineExtern`): what the lowering provides to
||| fragment code.
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Compiler.Native.Linkage.Routine` says what it is).
module Compiler.Native.Linkage.InlineExtern

import Compiler.Native.HeapObject.Enc as HeapObject
import Compiler.Native.HeapObject.Kind as HeapObject
import Compiler.Native.IRCommon.Area as IRCommon
import Compiler.Native.IRCommon.Intrinsic as IRCommon
import Compiler.Native.IRCommon.Op
import Compiler.Native.IRCommon.Ty as IRCommon
import Core.Name
import Core.Name.Namespace
import Data.Fin
import Data.List

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
    AreaAddress IRCommon.Area
  | ||| The pointer word of a uniform value known to be an object of the kind.
    ObjectWord HeapObject.Kind
  | ||| The uniform value of a pointer word to an object of the kind.
    WordObject HeapObject.Kind

||| An inline extern as the runtime library declares it: the registers of
||| its arguments, the token among them taking none, and of its result.
public export
record InlineExternSig (0 enc : HeapObject.Enc) where
  constructor MkInlineExternSig
  name : Name
  extern : InlineExtern
  params : List (IRCommon.Ty enc)
  results : List (IRCommon.Ty enc)

||| The inline externs, with their signatures.
export
inlineExterns : {0 enc : HeapObject.Enc} -> List (InlineExternSig enc)
inlineExterns =
  [ machine "Runtime.OS.Syscall" "prim__syscall6" (IRCommon.Intrinsic.Syscall 6)
  , memory "prim__load64" Load64 [IRCommon.Ty.W64, IRCommon.Ty.W64] [IRCommon.Ty.W64]
  , memory "prim__load32" (LoadNarrow IRCommon.Op.Sub32) [IRCommon.Ty.W64, IRCommon.Ty.W64] [IRCommon.Ty.W64]
  , memory "prim__load16" (LoadNarrow IRCommon.Op.Sub16) [IRCommon.Ty.W64, IRCommon.Ty.W64] [IRCommon.Ty.W64]
  , memory "prim__load8" (LoadNarrow IRCommon.Op.Sub8) [IRCommon.Ty.W64, IRCommon.Ty.W64] [IRCommon.Ty.W64]
  , memory "prim__store64" Store64 [IRCommon.Ty.W64, IRCommon.Ty.W64, IRCommon.Ty.W64] []
  , memory "prim__store32" (StoreNarrow IRCommon.Op.Sub32) [IRCommon.Ty.W64, IRCommon.Ty.W64, IRCommon.Ty.W64] []
  , memory "prim__store16" (StoreNarrow IRCommon.Op.Sub16) [IRCommon.Ty.W64, IRCommon.Ty.W64, IRCommon.Ty.W64] []
  , memory "prim__store8" (StoreNarrow IRCommon.Op.Sub8) [IRCommon.Ty.W64, IRCommon.Ty.W64, IRCommon.Ty.W64] []
  , machine "Runtime.Memory" "prim__getHp" IRCommon.Intrinsic.GetHp
  , machine "Runtime.Memory" "prim__setHp" IRCommon.Intrinsic.SetHp
  , machine "Runtime.Memory" "prim__getHpLim" IRCommon.Intrinsic.GetHpLim
  , machine "Runtime.Memory" "prim__setHpLim" IRCommon.Intrinsic.SetHpLim
  , machine "Runtime.Memory" "prim__getK" IRCommon.Intrinsic.GetK
  , machine "Runtime.Memory" "prim__setK" IRCommon.Intrinsic.SetK
  , memory "prim__pointerTag" PointerTag [] [IRCommon.Ty.W64]
  , memory "prim__stackLimitArea" (AreaAddress IRCommon.Area.STACK_LIMIT) [] [IRCommon.Ty.W64]
  , memory "prim__argvArea" (AreaAddress IRCommon.Area.ARGV) [] [IRCommon.Ty.W64]
  , memory "prim__rootsArea" (AreaAddress IRCommon.Area.ROOTS) [] [IRCommon.Ty.W64]
  , memory "prim__nrootsArea" (AreaAddress IRCommon.Area.NROOTS) [] [IRCommon.Ty.W64]
  , memory "prim__runtimeArea" (AreaAddress IRCommon.Area.RUNTIME) [] [IRCommon.Ty.W64]
  , memory "prim__stringWord" (ObjectWord HeapObject.Kind.STRING) [IRCommon.Ty.Val] [IRCommon.Ty.W64]
  , memory "prim__wordString" (WordObject HeapObject.Kind.STRING) [IRCommon.Ty.W64] [IRCommon.Ty.Val]
  , memory "prim__conWord" (ObjectWord HeapObject.Kind.CON) [IRCommon.Ty.Val] [IRCommon.Ty.W64]
  , memory "prim__wordCon" (WordObject HeapObject.Kind.CON) [IRCommon.Ty.W64] [IRCommon.Ty.Val] ]
  where
    sig : String -> String -> InlineExtern -> List (IRCommon.Ty enc) -> List (IRCommon.Ty enc) -> InlineExternSig enc
    sig ns n = MkInlineExternSig (NS (mkNamespace ns) (UN (Basic n)))

    memory : String -> InlineExtern -> List (IRCommon.Ty enc) -> List (IRCommon.Ty enc) -> InlineExternSig enc
    memory = sig "Runtime.Memory"

    word : IRCommon.Ty enc -> IRCommon.Ty enc
    word (IRCommon.Ty.PtrTo _) = IRCommon.Ty.W64
    word t = t

    -- an intrinsic's own signature, a pointer in it a word
    machine : String -> String -> IRCommon.Intrinsic -> InlineExternSig enc
    machine ns n i = sig ns n (Machine i) (map word (IRCommon.Intrinsic.params i)) (map word (IRCommon.Intrinsic.results i))

||| The inline extern a primitive of the runtime library is, by its name.
export
inlineExternOf : {0 enc : HeapObject.Enc} -> Name -> Maybe InlineExtern
inlineExternOf n = (.extern) <$> find (\i => i.name == n) (inlineExterns {enc})
