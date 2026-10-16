||| The inline externs (`Intrinsics`): the `%extern` primitives the runtime is
||| written with, which the lowering turns into instructions, never calls.
|||
||| Each takes words, or values as ordinary code holds them, and the token,
||| which has no register, last, and returns the token with its value, so
||| that its effect is ordered among the others by data dependence. A memory
||| access is at a base address plus a byte offset; a narrow load extends
||| the bits with zeros.
|||
||| This record of fields, one for each extern, its port the field's type,
||| is the contract. The runtime's memory module declares the externs,
||| privately, and gives the record of them (`Native.Runtime.Memory`'s
||| `intrinsics`), which checks each against its field's port; the code
||| generator reads that record, field by field, for the extern each field
||| holds, and lowers it as the field says. The raw system call is apart
||| (`Native.Syscall`), as only the platforms' modules may make one.
|||
||| Part of the contract between compiled code and the runtime, with the
||| heap-object model (`HeapObj.Shape` says what it is).
module Native.Intrinsics

import Native.Port

%default total

||| The inline externs, each a field of its port.
public export
record Intrinsics (f : Port -> Type) where
  constructor MkIntrinsics
  ||| A word, or 32, 16 or 8 bits, at a base address plus an offset.
  load64 : f (MkPort [Port.Word, Port.Word] (Just Port.Word))
  load32 : f (MkPort [Port.Word, Port.Word] (Just Port.Word))
  load16 : f (MkPort [Port.Word, Port.Word] (Just Port.Word))
  load8 : f (MkPort [Port.Word, Port.Word] (Just Port.Word))
  ||| A word, or its low 32, 16 or 8 bits, stored at a base address plus an
  ||| offset.
  store64 : f (MkPort [Port.Word, Port.Word, Port.Word] Nothing)
  store32 : f (MkPort [Port.Word, Port.Word, Port.Word] Nothing)
  store16 : f (MkPort [Port.Word, Port.Word, Port.Word] Nothing)
  store8 : f (MkPort [Port.Word, Port.Word, Port.Word] Nothing)
  ||| The allocation pointer and its limit, the pinned registers of the
  ||| allocation window.
  getHp : f (MkPort [] (Just Port.Word))
  setHp : f (MkPort [Port.Word] Nothing)
  getHpLim : f (MkPort [] (Just Port.Word))
  setHpLim : f (MkPort [Port.Word] Nothing)
  ||| The current continuation, a pinned register.
  getK : f (MkPort [] (Just Port.Word))
  setK : f (MkPort [Port.Word] Nothing)
  ||| The pointer tag of the program's encoding: what a pointer word is
  ||| beyond the object's address.
  pointerTag : f (MkPort [] (Just Port.Word))
  ||| The address of a per-thread area (`Native.Area`).
  stackLimitArea : f (MkPort [] (Just Port.Word))
  argvArea : f (MkPort [] (Just Port.Word))
  rootsArea : f (MkPort [] (Just Port.Word))
  nrootsArea : f (MkPort [] (Just Port.Word))
  runtimeArea : f (MkPort [] (Just Port.Word))
  ||| The word a value is, as ordinary code holds it, and the value a word
  ||| is: of any type, so the externs name none.
  valueWord : f (MkPort [Port.Value] (Just Port.Word))
  wordValue : f (MkPort [Port.Word] (Just Port.Value))

||| Each inline extern's entries of two records made one.
public export
zipIntrinsics : ({p : Port} -> f p -> g p -> h p) -> Intrinsics f -> Intrinsics g -> Intrinsics h
zipIntrinsics z a b =
  MkIntrinsics
    (z a.load64 b.load64) (z a.load32 b.load32) (z a.load16 b.load16) (z a.load8 b.load8)
    (z a.store64 b.store64) (z a.store32 b.store32) (z a.store16 b.store16) (z a.store8 b.store8)
    (z a.getHp b.getHp) (z a.setHp b.setHp) (z a.getHpLim b.getHpLim) (z a.setHpLim b.setHpLim)
    (z a.getK b.getK) (z a.setK b.setK) (z a.pointerTag b.pointerTag)
    (z a.stackLimitArea b.stackLimitArea) (z a.argvArea b.argvArea) (z a.rootsArea b.rootsArea)
    (z a.nrootsArea b.nrootsArea) (z a.runtimeArea b.runtimeArea)
    (z a.valueWord b.valueWord) (z a.wordValue b.wordValue)

||| The inline externs' entries, each with its port.
public export
intrinsicList : Intrinsics f -> List (p : Port ** f p)
intrinsicList r =
  [ (_ ** r.load64), (_ ** r.load32), (_ ** r.load16), (_ ** r.load8)
  , (_ ** r.store64), (_ ** r.store32), (_ ** r.store16), (_ ** r.store8)
  , (_ ** r.getHp), (_ ** r.setHp), (_ ** r.getHpLim), (_ ** r.setHpLim), (_ ** r.getK), (_ ** r.setK)
  , (_ ** r.pointerTag), (_ ** r.stackLimitArea), (_ ** r.argvArea), (_ ** r.rootsArea)
  , (_ ** r.nrootsArea), (_ ** r.runtimeArea)
  , (_ ** r.valueWord), (_ ** r.wordValue) ]
