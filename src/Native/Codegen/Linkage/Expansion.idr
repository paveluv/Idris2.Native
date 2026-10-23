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
import Native.Carrier
import Native.Codegen.IRCommon.Pinned as IRCommon
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Field
import Native.Intrinsic
import Native.Port
import Native.Rep
import Native.Types.Enc as Types
import Native.Width

%default total

||| What a pinned register carries across the boundary: the window's
||| registers are byte addresses, the continuation a value, which the
||| collector rewrites when it moves the continuation. The one table of the
||| pinned registers' carriers; their IR types refine it (`pinnedAgrees`).
public export
pinnedCarrier : IRCommon.Pinned -> Carrier
pinnedCarrier IRCommon.Pinned.Hp = Carrier.ByteAddr
pinnedCarrier IRCommon.Pinned.HpLim = Carrier.ByteAddr
pinnedCarrier IRCommon.Pinned.K = Carrier.Value

||| A pinned register's IR type refines what it carries: both say it is
||| held as the same rep, so no register crosses the contract as what the
||| IR does not take it for.
export
pinnedAgrees : {0 enc : Types.Enc} -> (r : IRCommon.Pinned) ->
               IRCommon.Ty.rep (IRCommon.Pinned.ty {enc} r) = Carrier.rep (pinnedCarrier r)
pinnedAgrees IRCommon.Pinned.Hp = Refl
pinnedAgrees IRCommon.Pinned.HpLim = Refl
pinnedAgrees IRCommon.Pinned.K = Refl

||| The instructions an inline extern expands to, by the port they
||| implement: what they take and give is the port's, each one the port of
||| an intrinsic it stands for, so that the port is stated once, there.
public export
data Expansion : Port -> Type where
  ||| Load the width at a base address plus an offset, extended with zeros.
  Load : Width -> Expansion (Intrinsic.port Intrinsic.Load64)
  ||| Store the width of a word at a base address plus an offset.
  Store : Width -> Expansion (Intrinsic.port Intrinsic.Store64)
  ||| Read a pinned register, as what it carries.
  Get : (r : IRCommon.Pinned) -> Expansion (() ~> MkField "register" (pinnedCarrier r))
  ||| Set a pinned register.
  Set : (r : IRCommon.Pinned) -> Expansion (MkField "register" (pinnedCarrier r) ~> ())
  ||| The pointer tag of the program's encoding: what a pointer word is
  ||| beyond the object's address.
  PointerTag : Expansion (Intrinsic.port Intrinsic.PointerTag)
  ||| The address of an area.
  AreaAddress : Area -> Expansion (Intrinsic.port Intrinsic.RuntimeArea)
  ||| The number of the program's top-level constants.
  ConstantCount : Expansion (Intrinsic.port Intrinsic.ConstantCount)
  ||| The word a uniform value is.
  ValueWord : Expansion (Intrinsic.port Intrinsic.ValueWord)
  ||| The uniform value a word is.
  WordValue : Expansion (Intrinsic.port Intrinsic.WordValue)
  ||| The machine's system call, of six arguments.
  Syscall : Expansion (Intrinsic.port Intrinsic.Syscall6)

||| Each intrinsic's expansion, of its port.
export
expansion : (i : Intrinsic) -> Expansion (Intrinsic.port i)
expansion Intrinsic.Load64 = Load Width.Whole
expansion Intrinsic.Load32 = Load (Width.Narrow Width.Sub32)
expansion Intrinsic.Load16 = Load (Width.Narrow Width.Sub16)
expansion Intrinsic.Load8 = Load (Width.Narrow Width.Sub8)
expansion Intrinsic.Store64 = Store Width.Whole
expansion Intrinsic.Store32 = Store (Width.Narrow Width.Sub32)
expansion Intrinsic.Store16 = Store (Width.Narrow Width.Sub16)
expansion Intrinsic.Store8 = Store (Width.Narrow Width.Sub8)
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
expansion Intrinsic.ConstantsArea = AreaAddress Area.CONSTANTS
expansion Intrinsic.ConstantCount = ConstantCount
expansion ValueWord = ValueWord
expansion WordValue = WordValue
expansion Intrinsic.Syscall6 = Syscall
