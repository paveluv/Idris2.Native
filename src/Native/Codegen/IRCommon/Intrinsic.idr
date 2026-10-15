||| The intrinsics: operations on machine state that the runtime needs and no
||| instruction expresses (`Intrinsic`), with what each takes and gives.
|||
||| Part of the vocabulary the native backend's two IRs share
||| (`Native.Codegen.IRCommon.Ty` says what it is).
module Native.Codegen.IRCommon.Intrinsic

import Native.Codegen.IRCommon.Ty

import Data.Fin
import Data.List
import Native.HeapObj.Enc as HeapObj
import Native.HeapObj.Kind

%default total

||| Operations on machine state that the runtime needs and no instruction
||| expresses. Each is a fixed instruction sequence per target, never a call,
||| and takes and gives what `params` and `results` say. The two IRs have
||| one instruction for them all, on this list.
public export
data Intrinsic
  = ||| The allocation pointer.
    GetHp
  | ||| Set the allocation pointer.
    SetHp
  | ||| The allocation limit.
    GetHpLim
  | ||| Set the allocation limit.
    SetHpLim
  | ||| The current continuation (heap lowering).
    GetK
  | ||| Set the current continuation: how the collector publishes a
    ||| continuation it has moved.
    SetK
  | ||| One system call of so many arguments, at most six: its number, then
    ||| the arguments, giving its result. A collection never starts in a
    ||| system call.
    Syscall (Fin 7)

public export
Show Intrinsic where
  show GetHp = "getHp"
  show SetHp = "setHp"
  show GetHpLim = "getHpLim"
  show SetHpLim = "setHpLim"
  show GetK = "getK"
  show SetK = "setK"
  show (Syscall _) = "syscall"

namespace Intrinsic
  ||| What an intrinsic takes, in order.
  public export
  params : Intrinsic -> List (Ty enc)
  params GetHp = []
  params SetHp = [Ty.W64]
  params GetHpLim = []
  params SetHpLim = [Ty.W64]
  params GetK = []
  params SetK = [Ty.PtrTo HeapObj.Kind.CONT]
  params (Syscall n) = replicate (S (finToNat n)) Ty.W64

  ||| What an intrinsic gives, in order.
  public export
  results : Intrinsic -> List (Ty enc)
  results GetHp = [Ty.W64]
  results SetHp = []
  results GetHpLim = [Ty.W64]
  results SetHpLim = []
  results GetK = [Ty.PtrTo HeapObj.Kind.CONT]
  results SetK = []
  results (Syscall _) = [Ty.W64]
