||| How the lowering provides the inline externs of the contract
||| (`InlineExtern`, `lowerings`): the instruction each stands for.
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Native.Codegen.Linkage.Routine` says what it is).
module Native.Codegen.Linkage.InlineExtern

import Data.Fin
import Native.Area
import Native.Codegen.IRCommon.Intrinsic as IRCommon
import Native.Codegen.IRCommon.Op
import Native.Intrinsics
import Native.Port

%default total

||| The instruction an inline extern stands for (`Native.Intrinsics` says
||| what the externs are).
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
  | ||| The word a uniform value is.
    ValueWord
  | ||| The uniform value a word is.
    WordValue

||| How the lowering provides each inline extern of the contract
||| (`Native.Intrinsics`): the field's instruction, the registers its port's.
export
lowerings : Intrinsics (\_ => InlineExtern)
lowerings =
  MkIntrinsics
    { syscall6 = Machine (IRCommon.Intrinsic.Syscall 6)
    , load64 = Load64, load32 = LoadNarrow IRCommon.Op.Sub32, load16 = LoadNarrow IRCommon.Op.Sub16
    , load8 = LoadNarrow IRCommon.Op.Sub8
    , store64 = Store64, store32 = StoreNarrow IRCommon.Op.Sub32, store16 = StoreNarrow IRCommon.Op.Sub16
    , store8 = StoreNarrow IRCommon.Op.Sub8
    , getHp = Machine IRCommon.Intrinsic.GetHp, setHp = Machine IRCommon.Intrinsic.SetHp
    , getHpLim = Machine IRCommon.Intrinsic.GetHpLim, setHpLim = Machine IRCommon.Intrinsic.SetHpLim
    , getK = Machine IRCommon.Intrinsic.GetK, setK = Machine IRCommon.Intrinsic.SetK
    , pointerTag = PointerTag
    , stackLimitArea = AreaAddress Area.STACK_LIMIT, argvArea = AreaAddress Area.ARGV
    , rootsArea = AreaAddress Area.ROOTS, nrootsArea = AreaAddress Area.NROOTS
    , runtimeArea = AreaAddress Area.RUNTIME
    , valueWord = ValueWord, wordValue = WordValue }
