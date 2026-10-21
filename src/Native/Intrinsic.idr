||| The inline externs (`Intrinsic`): the `%extern` primitives the runtime is
||| written with, which the lowering turns into instructions, never calls.
|||
||| This module is the contract for them, and the only place it is stated:
||| which intrinsics there are, and each one's arrow (`port`). The runtime
||| declares each extern by its port (`%extern intrinsic__store64 : PortTy
||| (port Store64)` in `Native.Runtime.Memory`), which Idris checks; the code
||| generator finds each extern by that type alone, and lowers it as
||| `Native.Codegen.Linkage.Expansion` says, which Idris checks against the
||| same port. Neither side restates it.
|||
||| Each takes words, byte addresses or values as ordinary code holds them,
||| and returns its value; the runtime adds the token that orders them. A
||| memory access is at a base byte address plus a byte offset; a narrow load
||| extends the bits with zeros. The direct system call is one of them, though
||| only the platforms' modules may make one (the linter's `syscall`).
|||
||| Part of the contract between compiled code and the runtime, with the
||| heap-object model (`HeapObj.Shape` says what it is).
module Native.Intrinsic

import Native.Carrier
import Native.Mach
import Native.Port

import Data.List.Elem

%default total

||| The inline externs.
public export
data Intrinsic
  = ||| A word, or 32, 16 or 8 bits, at a base address plus an offset.
    Load64 | Load32 | Load16 | Load8
  | ||| A word, or its low 32, 16 or 8 bits, stored at a base address plus an
    ||| offset.
    Store64 | Store32 | Store16 | Store8
  | ||| The allocation pointer and its limit, the pinned registers of the
    ||| allocation window, and the current continuation, a pinned register.
    GetHp | SetHp | GetHpLim | SetHpLim | GetK | SetK
  | ||| The pointer tag of the program's encoding: what a pointer word is
    ||| beyond the object's address.
    PointerTag
  | ||| The address of an area (`Native.Area`).
    StackLimitArea | ArgvArea | RootsArea | NrootsArea | RuntimeArea | ConstantsArea
  | ||| The number of the program's top-level constants, the cells of
    ||| `Area.CONSTANTS`, which the code generator knows.
    ConstantCount
  | ||| The word a value is, as ordinary code holds it, and the value a word
    ||| is: of any type, so the externs name none.
    ValueWord | WordValue
  | ||| A system call: its number and six arguments; its result.
    Syscall6

||| Each intrinsic's arrow: what its arguments and its result carry.
public export
port : Intrinsic -> Port
port Load64 = MkPort [Carrier.ByteAddr, Carrier.Machine Mach.U64] (Just (Carrier.Machine Mach.U64))
port Load32 = MkPort [Carrier.ByteAddr, Carrier.Machine Mach.U64] (Just (Carrier.Machine Mach.U64))
port Load16 = MkPort [Carrier.ByteAddr, Carrier.Machine Mach.U64] (Just (Carrier.Machine Mach.U64))
port Load8 = MkPort [Carrier.ByteAddr, Carrier.Machine Mach.U64] (Just (Carrier.Machine Mach.U64))
port Store64 = MkPort [Carrier.ByteAddr, Carrier.Machine Mach.U64, Carrier.Machine Mach.U64] Nothing
port Store32 = MkPort [Carrier.ByteAddr, Carrier.Machine Mach.U64, Carrier.Machine Mach.U64] Nothing
port Store16 = MkPort [Carrier.ByteAddr, Carrier.Machine Mach.U64, Carrier.Machine Mach.U64] Nothing
port Store8 = MkPort [Carrier.ByteAddr, Carrier.Machine Mach.U64, Carrier.Machine Mach.U64] Nothing
port GetHp = MkPort [] (Just Carrier.ByteAddr)
port SetHp = MkPort [Carrier.ByteAddr] Nothing
port GetHpLim = MkPort [] (Just Carrier.ByteAddr)
port SetHpLim = MkPort [Carrier.ByteAddr] Nothing
port GetK = MkPort [] (Just (Carrier.Machine Mach.U64))
port SetK = MkPort [Carrier.Machine Mach.U64] Nothing
port PointerTag = MkPort [] (Just (Carrier.Machine Mach.U64))
port StackLimitArea = MkPort [] (Just Carrier.ByteAddr)
port ArgvArea = MkPort [] (Just Carrier.ByteAddr)
port RootsArea = MkPort [] (Just Carrier.ByteAddr)
port NrootsArea = MkPort [] (Just Carrier.ByteAddr)
port RuntimeArea = MkPort [] (Just Carrier.ByteAddr)
port ConstantsArea = MkPort [] (Just Carrier.ByteAddr)
port ConstantCount = MkPort [] (Just (Carrier.Machine Mach.U64))
port ValueWord = MkPort [Carrier.Value] (Just (Carrier.Machine Mach.U64))
port WordValue = MkPort [Carrier.Machine Mach.U64] (Just Carrier.Value)
port Syscall6 =
  MkPort [Carrier.Machine Mach.U64,
    Carrier.Machine Mach.U64, Carrier.Machine Mach.U64, Carrier.Machine Mach.U64,
          Carrier.Machine Mach.U64, Carrier.Machine Mach.U64, Carrier.Machine Mach.U64]
    (Just (Carrier.Machine Mach.U64))

||| Every intrinsic, once. The code generator pairs this list's term, as the
||| loaded runtime's context holds it, with its own copy, element by element:
||| one declaration on both sides, so a constructor it reads is the one it
||| has, whatever the order.
public export
allIntrinsics : List Intrinsic
allIntrinsics =
  [ Load64, Load32, Load16, Load8, Store64, Store32, Store16, Store8
  , GetHp, SetHp, GetHpLim, SetHpLim, GetK, SetK, PointerTag
  , StackLimitArea, ArgvArea, RootsArea, NrootsArea, RuntimeArea, ConstantsArea, ConstantCount
  , ValueWord, WordValue, Syscall6 ]

||| The list holds every intrinsic.
complete : (i : Intrinsic) -> Elem i Intrinsic.allIntrinsics
complete Load64 = %search
complete Load32 = %search
complete Load16 = %search
complete Load8 = %search
complete Store64 = %search
complete Store32 = %search
complete Store16 = %search
complete Store8 = %search
complete GetHp = %search
complete SetHp = %search
complete GetHpLim = %search
complete SetHpLim = %search
complete GetK = %search
complete SetK = %search
complete PointerTag = %search
complete StackLimitArea = %search
complete ArgvArea = %search
complete RootsArea = %search
complete NrootsArea = %search
complete RuntimeArea = %search
complete ConstantsArea = %search
complete ConstantCount = %search
complete ValueWord = %search
complete WordValue = %search
complete Syscall6 = %search
