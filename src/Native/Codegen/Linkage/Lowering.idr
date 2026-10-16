||| How the lowering provides each inline extern of the contract
||| (`Native.Intrinsic`): the instructions it stands for (`Lowering`), each
||| indexed by the port it implements, and the one for each intrinsic
||| (`lowering`), which Idris checks against the intrinsic's port, as it
||| checks the runtime's extern against it.
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Native.Codegen.Linkage.Routine` says what it is).
module Native.Codegen.Linkage.Lowering

import Native.Area
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Pinned as IRCommon
import Native.Intrinsic
import Native.Port

%default total

||| How much of a word a memory access moves: all of it, or its low 32, 16
||| or 8 bits.
public export
data Width = Whole | Narrow IRCommon.Op.SubWord

||| What a pinned register carries across the boundary: the window's
||| registers are raw addresses, the continuation its pointer word.
public export
pinnedCarrier : IRCommon.Pinned -> Port.Carrier
pinnedCarrier IRCommon.Pinned.Hp = Port.Raw
pinnedCarrier IRCommon.Pinned.HpLim = Port.Raw
pinnedCarrier IRCommon.Pinned.K = Port.Word

||| The instructions an inline extern stands for, by the port they
||| implement: what they take and give is the port's.
public export
data Lowering : Port -> Type where
  ||| Load the width at a base address plus an offset, extended with zeros.
  Load : Width -> Lowering (MkPort [Port.Raw, Port.Word] (Just Port.Word))
  ||| Store the width of a word at a base address plus an offset.
  Store : Width -> Lowering (MkPort [Port.Raw, Port.Word, Port.Word] Nothing)
  ||| Read a pinned register, as what it carries.
  Get : (r : IRCommon.Pinned) -> Lowering (MkPort [] (Just (pinnedCarrier r)))
  ||| Set a pinned register.
  Set : (r : IRCommon.Pinned) -> Lowering (MkPort [pinnedCarrier r] Nothing)
  ||| The pointer tag of the program's encoding: what a pointer word is
  ||| beyond the object's address.
  PointerTag : Lowering (MkPort [] (Just Port.Word))
  ||| The address of a per-thread area.
  AreaAddress : Area -> Lowering (MkPort [] (Just Port.Raw))
  ||| The word a uniform value is.
  ValueWord : Lowering (MkPort [Port.Value] (Just Port.Word))
  ||| The uniform value a word is.
  WordValue : Lowering (MkPort [Port.Word] (Just Port.Value))
  ||| The machine's system call, of six arguments.
  Syscall : Lowering (MkPort [Port.Word, Port.Word, Port.Word, Port.Word, Port.Word, Port.Word, Port.Word]
                             (Just Port.Word))

||| Each intrinsic's lowering, of its port.
export
lowering : (i : Intrinsic) -> Lowering (Intrinsic.port i)
lowering Intrinsic.Load64 = Load Whole
lowering Intrinsic.Load32 = Load (Narrow IRCommon.Op.Sub32)
lowering Intrinsic.Load16 = Load (Narrow IRCommon.Op.Sub16)
lowering Intrinsic.Load8 = Load (Narrow IRCommon.Op.Sub8)
lowering Intrinsic.Store64 = Store Whole
lowering Intrinsic.Store32 = Store (Narrow IRCommon.Op.Sub32)
lowering Intrinsic.Store16 = Store (Narrow IRCommon.Op.Sub16)
lowering Intrinsic.Store8 = Store (Narrow IRCommon.Op.Sub8)
lowering Intrinsic.GetHp = Get IRCommon.Pinned.Hp
lowering Intrinsic.SetHp = Set IRCommon.Pinned.Hp
lowering Intrinsic.GetHpLim = Get IRCommon.Pinned.HpLim
lowering Intrinsic.SetHpLim = Set IRCommon.Pinned.HpLim
lowering Intrinsic.GetK = Get IRCommon.Pinned.K
lowering Intrinsic.SetK = Set IRCommon.Pinned.K
lowering PointerTag = PointerTag
lowering Intrinsic.StackLimitArea = AreaAddress Area.STACK_LIMIT
lowering Intrinsic.ArgvArea = AreaAddress Area.ARGV
lowering Intrinsic.RootsArea = AreaAddress Area.ROOTS
lowering Intrinsic.NrootsArea = AreaAddress Area.NROOTS
lowering Intrinsic.RuntimeArea = AreaAddress Area.RUNTIME
lowering ValueWord = ValueWord
lowering WordValue = WordValue
lowering Intrinsic.Syscall6 = Syscall
