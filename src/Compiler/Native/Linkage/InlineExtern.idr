||| The inline externs (`InlineExtern`): what the lowering provides to
||| fragment code.
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Compiler.Native.Linkage.Routine` says what it is).
module Compiler.Native.Linkage.InlineExtern

import Compiler.Native.HeapObject.Enc
import Compiler.Native.HeapObject.Kind
import Compiler.Native.IRCommon.Area
import Compiler.Native.IRCommon.Intrinsic
import Compiler.Native.IRCommon.Operators
import Compiler.Native.IRCommon.Ty
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
    Machine Intrinsic
  | ||| Load a word.
    Load64
  | ||| Load 8, 16 or 32 bits.
    LoadNarrow SubWord
  | ||| Store a word.
    Store64
  | ||| Store a word's low 8, 16 or 32 bits.
    StoreNarrow SubWord
  | ||| The pointer tag of the program's encoding: what a pointer word is
    ||| beyond the object's address.
    PointerTag
  | ||| The address of a per-thread area.
    AreaAddress Area
  | ||| The pointer word of a uniform value known to be an object of the kind.
    ObjectWord Kind
  | ||| The uniform value of a pointer word to an object of the kind.
    WordObject Kind

||| An inline extern as the runtime library declares it: the registers of
||| its arguments, the token among them taking none, and of its result.
public export
record InlineExternSig (0 enc : Enc) where
  constructor MkInlineExternSig
  name : Name
  extern : InlineExtern
  params : List (Ty enc)
  results : List (Ty enc)

||| The inline externs, with their signatures.
export
inlineExterns : {0 enc : Enc} -> List (InlineExternSig enc)
inlineExterns =
  [ machine "Runtime.OS.Syscall" "prim__syscall6" (Syscall 6)
  , memory "prim__load64" Load64 [W64, W64] [W64]
  , memory "prim__load32" (LoadNarrow Sub32) [W64, W64] [W64]
  , memory "prim__load16" (LoadNarrow Sub16) [W64, W64] [W64]
  , memory "prim__load8" (LoadNarrow Sub8) [W64, W64] [W64]
  , memory "prim__store64" Store64 [W64, W64, W64] []
  , memory "prim__store32" (StoreNarrow Sub32) [W64, W64, W64] []
  , memory "prim__store16" (StoreNarrow Sub16) [W64, W64, W64] []
  , memory "prim__store8" (StoreNarrow Sub8) [W64, W64, W64] []
  , machine "Runtime.Memory" "prim__getHp" GetHp
  , machine "Runtime.Memory" "prim__setHp" SetHp
  , machine "Runtime.Memory" "prim__getHpLim" GetHpLim
  , machine "Runtime.Memory" "prim__setHpLim" SetHpLim
  , machine "Runtime.Memory" "prim__getK" GetK
  , machine "Runtime.Memory" "prim__setK" SetK
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
    sig : String -> String -> InlineExtern -> List (Ty enc) -> List (Ty enc) -> InlineExternSig enc
    sig ns n = MkInlineExternSig (NS (mkNamespace ns) (UN (Basic n)))

    memory : String -> InlineExtern -> List (Ty enc) -> List (Ty enc) -> InlineExternSig enc
    memory = sig "Runtime.Memory"

    word : Ty enc -> Ty enc
    word (PtrTo _) = W64
    word t = t

    -- an intrinsic's own signature, a pointer in it a word
    machine : String -> String -> Intrinsic -> InlineExternSig enc
    machine ns n i = sig ns n (Machine i) (map word (Intrinsic.params i)) (map word (Intrinsic.results i))

||| The inline extern a primitive of the runtime library is, by its name.
export
inlineExternOf : {0 enc : Enc} -> Name -> Maybe InlineExtern
inlineExternOf n = (.extern) <$> find (\i => i.name == n) (inlineExterns {enc})
