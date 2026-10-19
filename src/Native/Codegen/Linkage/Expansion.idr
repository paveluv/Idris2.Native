||| How the lowering provides each inline extern of the contract
||| (`Native.Intrinsic`): the instructions it expands to (`Expansion`), each
||| indexed by the port it implements, and the one for each intrinsic
||| (`expansion`), which Idris checks against the intrinsic's port, as it
||| checks the runtime's extern against it.
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Native.Codegen.Linkage.Routine` says what it is).
module Native.Codegen.Linkage.Expansion

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

||| The instructions an inline extern expands to, by the port they
||| implement: what they take and give is the port's.
public export
data Expansion : Port -> Type where
  ||| Load the width at a base address plus an offset, extended with zeros.
  Load : Width -> Expansion (MkPort [Port.Raw, Port.Word] (Just Port.Word))
  ||| Store the width of a word at a base address plus an offset.
  Store : Width -> Expansion (MkPort [Port.Raw, Port.Word, Port.Word] Nothing)
  ||| Read a pinned register, as what it carries.
  Get : (r : IRCommon.Pinned) -> Expansion (MkPort [] (Just (pinnedCarrier r)))
  ||| Set a pinned register.
  Set : (r : IRCommon.Pinned) -> Expansion (MkPort [pinnedCarrier r] Nothing)
  ||| The pointer tag of the program's encoding: what a pointer word is
  ||| beyond the object's address.
  PointerTag : Expansion (MkPort [] (Just Port.Word))
  ||| The address of a per-thread area.
  AreaAddress : Area -> Expansion (MkPort [] (Just Port.Raw))
  ||| The word a uniform value is.
  ValueWord : Expansion (MkPort [Port.Value] (Just Port.Word))
  ||| The uniform value a word is.
  WordValue : Expansion (MkPort [Port.Word] (Just Port.Value))
  ||| The machine's system call, of six arguments.
  Syscall : Expansion
            (MkPort [Port.Word, Port.Word, Port.Word, Port.Word, Port.Word, Port.Word, Port.Word]
                             (Just Port.Word))

||| Each intrinsic's expansion, of its port.
export
expansion : (i : Intrinsic) -> Expansion (Intrinsic.port i)
expansion Intrinsic.Load64 = Load Whole
expansion Intrinsic.Load32 = Load (Narrow IRCommon.Op.Sub32)
expansion Intrinsic.Load16 = Load (Narrow IRCommon.Op.Sub16)
expansion Intrinsic.Load8 = Load (Narrow IRCommon.Op.Sub8)
expansion Intrinsic.Store64 = Store Whole
expansion Intrinsic.Store32 = Store (Narrow IRCommon.Op.Sub32)
expansion Intrinsic.Store16 = Store (Narrow IRCommon.Op.Sub16)
expansion Intrinsic.Store8 = Store (Narrow IRCommon.Op.Sub8)
expansion Intrinsic.GetHp = Get IRCommon.Pinned.Hp
expansion Intrinsic.SetHp = Set IRCommon.Pinned.Hp
expansion Intrinsic.GetHpLim = Get IRCommon.Pinned.HpLim
expansion Intrinsic.SetHpLim = Set IRCommon.Pinned.HpLim
expansion Intrinsic.GetK = Get IRCommon.Pinned.K
expansion Intrinsic.SetK = Set IRCommon.Pinned.K
expansion PointerTag = PointerTag
expansion Intrinsic.StackLimitArea = AreaAddress Area.STACK_LIMIT
expansion Intrinsic.ArgvArea = AreaAddress Area.ARGV
expansion Intrinsic.RootsArea = AreaAddress Area.ROOTS
expansion Intrinsic.NrootsArea = AreaAddress Area.NROOTS
expansion Intrinsic.RuntimeArea = AreaAddress Area.RUNTIME
expansion ValueWord = ValueWord
expansion WordValue = WordValue
expansion Intrinsic.Syscall6 = Syscall
