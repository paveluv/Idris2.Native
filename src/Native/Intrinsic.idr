||| The inline externs (`Intrinsic`): the `%extern` primitives the runtime is
||| written with, which the lowering turns into instructions, never calls.
|||
||| This module is the contract for them, and the only place it is stated:
||| which intrinsics there are, and each one's arrow (`port`). The runtime
||| declares each extern by its port (`%extern intrinsic__store64 : ExternTy
||| (port Store64)` in `Native.Runtime.Memory`), which Idris checks; the code
||| generator finds each extern by that type alone, and lowers it as
||| `Native.Codegen.Linkage.Lowering` says, which Idris checks against the
||| same port. Neither side restates it.
|||
||| Each takes words, raw addresses or values as ordinary code holds them,
||| and returns its value; the runtime adds the token that orders them. A
||| memory access is at a raw base address plus a byte offset; a narrow
||| load extends the bits with zeros. The raw system call is one of them, though only the
||| platforms' modules may make one (the linter's `syscall`).
|||
||| Part of the contract between compiled code and the runtime, with the
||| heap-object model (`HeapObj.Shape` says what it is).
module Native.Intrinsic

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
  | ||| The address of a per-thread area (`Native.Area`).
    StackLimitArea | ArgvArea | RootsArea | NrootsArea | RuntimeArea
  | ||| The word a value is, as ordinary code holds it, and the value a word
    ||| is: of any type, so the externs name none.
    ValueWord | WordValue
  | ||| A system call: its number and six arguments; its result.
    Syscall6

||| Each intrinsic's arrow: what its arguments and its result carry.
public export
port : Intrinsic -> Port
port Load64 = MkPort [Port.Raw, Port.Word] (Just Port.Word)
port Load32 = MkPort [Port.Raw, Port.Word] (Just Port.Word)
port Load16 = MkPort [Port.Raw, Port.Word] (Just Port.Word)
port Load8 = MkPort [Port.Raw, Port.Word] (Just Port.Word)
port Store64 = MkPort [Port.Raw, Port.Word, Port.Word] Nothing
port Store32 = MkPort [Port.Raw, Port.Word, Port.Word] Nothing
port Store16 = MkPort [Port.Raw, Port.Word, Port.Word] Nothing
port Store8 = MkPort [Port.Raw, Port.Word, Port.Word] Nothing
port GetHp = MkPort [] (Just Port.Raw)
port SetHp = MkPort [Port.Raw] Nothing
port GetHpLim = MkPort [] (Just Port.Raw)
port SetHpLim = MkPort [Port.Raw] Nothing
port GetK = MkPort [] (Just Port.Word)
port SetK = MkPort [Port.Word] Nothing
port PointerTag = MkPort [] (Just Port.Word)
port StackLimitArea = MkPort [] (Just Port.Raw)
port ArgvArea = MkPort [] (Just Port.Raw)
port RootsArea = MkPort [] (Just Port.Raw)
port NrootsArea = MkPort [] (Just Port.Raw)
port RuntimeArea = MkPort [] (Just Port.Raw)
port ValueWord = MkPort [Port.Value] (Just Port.Word)
port WordValue = MkPort [Port.Word] (Just Port.Value)
port Syscall6 =
  MkPort [Port.Word, Port.Word, Port.Word, Port.Word, Port.Word, Port.Word, Port.Word] (Just Port.Word)

||| Every intrinsic, once. The code generator pairs this list's term, as the
||| loaded runtime's context holds it, with its own copy, element by element:
||| one declaration on both sides, so a constructor it reads is the one it
||| has, whatever the order.
public export
allIntrinsics : List Intrinsic
allIntrinsics =
  [ Load64, Load32, Load16, Load8, Store64, Store32, Store16, Store8
  , GetHp, SetHp, GetHpLim, SetHpLim, GetK, SetK, PointerTag
  , StackLimitArea, ArgvArea, RootsArea, NrootsArea, RuntimeArea, ValueWord, WordValue, Syscall6 ]

||| The list holds every intrinsic.
export
complete : (i : Intrinsic) -> Elem i Intrinsic.allIntrinsics
complete Load64 = Here
complete Load32 = There (Here)
complete Load16 = There (There (Here))
complete Load8 = There (There (There (Here)))
complete Store64 = There (There (There (There (Here))))
complete Store32 = There (There (There (There (There (Here)))))
complete Store16 = There (There (There (There (There (There (Here))))))
complete Store8 = There (There (There (There (There (There (There (Here)))))))
complete GetHp = There (There (There (There (There (There (There (There (Here))))))))
complete SetHp = There (There (There (There (There (There (There (There (There (Here)))))))))
complete GetHpLim = There (There (There (There (There (There (There (There (There (There (Here))))))))))
complete SetHpLim = There (There (There (There (There (There (There (There (There (There (There (Here)))))))))))
complete GetK = There (There (There (There (There (There (There (There (There (There (There (There (Here))))))))))))
complete SetK = There (There (There (There (There (There (There (There (There (There (There (There (There (Here)))))))))))))
complete PointerTag = There (There (There (There (There (There (There (There (There (There (There (There (There (There (Here))))))))))))))
complete StackLimitArea = There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (Here)))))))))))))))
complete ArgvArea = There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (Here))))))))))))))))
complete RootsArea = There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (Here)))))))))))))))))
complete NrootsArea = There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (Here))))))))))))))))))
complete RuntimeArea = There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (Here)))))))))))))))))))
complete ValueWord = There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (Here))))))))))))))))))))
complete WordValue = There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (Here)))))))))))))))))))))
complete Syscall6 = There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (There (Here))))))))))))))))))))))
