||| The inline externs (`Intrinsics`): the `%extern` primitives the runtime is
||| written with, which the lowering turns into instructions, never calls.
|||
||| Each takes words, or values as ordinary code holds them, and the token,
||| which has no register, last, and returns the token with its value, so
||| that its effect is ordered among the others by data dependence. A memory
||| access is at a base address plus a byte offset; a narrow load extends
||| the bits with zeros.
|||
||| The externs are declared here, of the contract, and the record of them
||| (`intrinsics`) checks each against its field's port. The code generator
||| reads the record, field by field, for the extern each field holds, and
||| lowers it as the field says. Only the runtime's memory module imports
||| this one (the linter's `intrinsics`): the rest of the runtime reaches
||| memory through it, by typed addresses.
|||
||| Part of the contract between compiled code and the runtime, with the
||| heap-object model (`HeapObj.Enc` says what it is).
module Native.Intrinsics

import Native.Flat.Uniform as Flat
import Native.Heap
import Native.HeapObj.Kind as HeapObj
import Native.Port
import Native.Syscall

%default total

export
%extern prim__load64 : (base, offset : Bits64) -> (1 m : Heap) -> Heap.Ret Heap Bits64
export
%extern prim__load32 : (base, offset : Bits64) -> (1 m : Heap) -> Heap.Ret Heap Bits64
export
%extern prim__load16 : (base, offset : Bits64) -> (1 m : Heap) -> Heap.Ret Heap Bits64
export
%extern prim__load8 : (base, offset : Bits64) -> (1 m : Heap) -> Heap.Ret Heap Bits64
export
%extern prim__store64 : (base, offset, value : Bits64) -> (1 m : Heap) -> Heap.Ret Heap ()
export
%extern prim__store32 : (base, offset, value : Bits64) -> (1 m : Heap) -> Heap.Ret Heap ()
export
%extern prim__store16 : (base, offset, value : Bits64) -> (1 m : Heap) -> Heap.Ret Heap ()
export
%extern prim__store8 : (base, offset, value : Bits64) -> (1 m : Heap) -> Heap.Ret Heap ()

export
%extern prim__getHp : (1 m : Heap) -> Heap.Ret Heap Bits64
export
%extern prim__setHp : (hp : Bits64) -> (1 m : Heap) -> Heap.Ret Heap ()
export
%extern prim__getHpLim : (1 m : Heap) -> Heap.Ret Heap Bits64
export
%extern prim__setHpLim : (hplim : Bits64) -> (1 m : Heap) -> Heap.Ret Heap ()
export
%extern prim__getK : (1 m : Heap) -> Heap.Ret Heap Bits64
export
%extern prim__setK : (k : Bits64) -> (1 m : Heap) -> Heap.Ret Heap ()
export
%extern prim__pointerTag : (1 m : Heap) -> Heap.Ret Heap Bits64
export
%extern prim__stackLimitArea : (1 m : Heap) -> Heap.Ret Heap Bits64
export
%extern prim__argvArea : (1 m : Heap) -> Heap.Ret Heap Bits64
export
%extern prim__rootsArea : (1 m : Heap) -> Heap.Ret Heap Bits64
export
%extern prim__nrootsArea : (1 m : Heap) -> Heap.Ret Heap Bits64
export
%extern prim__runtimeArea : (1 m : Heap) -> Heap.Ret Heap Bits64

export
%extern prim__valueWord : {0 a : Type} -> Flat.Uniform a -> (1 m : Heap) -> Heap.Ret Heap Bits64
export
%extern prim__wordValue : {0 a : Type} -> Bits64 -> (1 m : Heap) -> Heap.Ret Heap (Flat.Uniform a)

||| The inline externs, each a field of its port.
public export
record Intrinsics (f : Port -> Type) where
  constructor MkIntrinsics
  ||| A system call: its number and six arguments; its result.
  syscall6 : f
             (MkPort [Port.Word, Port.Word, Port.Word, Port.Word, Port.Word, Port.Word, Port.Word]
              (Just Port.Word))
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

||| The externs, each checked against its field's port.
public export
intrinsics : Intrinsics Port.ExternTy
intrinsics =
  MkIntrinsics
    { syscall6 = Syscall.prim__syscall6
    , load64 = prim__load64, load32 = prim__load32, load16 = prim__load16, load8 = prim__load8
    , store64 = prim__store64, store32 = prim__store32, store16 = prim__store16, store8 = prim__store8
    , getHp = prim__getHp, setHp = prim__setHp, getHpLim = prim__getHpLim, setHpLim = prim__setHpLim
    , getK = prim__getK, setK = prim__setK
    , pointerTag = prim__pointerTag
    , stackLimitArea = prim__stackLimitArea, argvArea = prim__argvArea, rootsArea = prim__rootsArea
    , nrootsArea = prim__nrootsArea, runtimeArea = prim__runtimeArea
    , valueWord = prim__valueWord, wordValue = prim__wordValue }

||| Each inline extern's entries of two records made one.
public export
zipIntrinsics : ({p : Port} -> f p -> g p -> h p) -> Intrinsics f -> Intrinsics g -> Intrinsics h
zipIntrinsics z a b =
  MkIntrinsics (z a.syscall6 b.syscall6)
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
  [ (_ ** r.syscall6), (_ ** r.load64), (_ ** r.load32), (_ ** r.load16), (_ ** r.load8)
  , (_ ** r.store64), (_ ** r.store32), (_ ** r.store16), (_ ** r.store8)
  , (_ ** r.getHp), (_ ** r.setHp), (_ ** r.getHpLim), (_ ** r.setHpLim), (_ ** r.getK), (_ ** r.setK)
  , (_ ** r.pointerTag), (_ ** r.stackLimitArea), (_ ** r.argvArea), (_ ** r.rootsArea)
  , (_ ** r.nrootsArea), (_ ** r.runtimeArea)
  , (_ ** r.valueWord), (_ ** r.wordValue) ]
