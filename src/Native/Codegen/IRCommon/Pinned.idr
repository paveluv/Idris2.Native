||| The registers the code generator pins for the runtime (`Pinned`): the
||| allocation window's pointer and limit, and the current continuation,
||| under the heap lowering. Generated code and the runtime both read and set
||| them, and no other code uses them.
|||
||| Part of the vocabulary the native backend's two IRs share
||| (`Native.Codegen.IRCommon.Ty` says what it is).
module Native.Codegen.IRCommon.Pinned

import Native.Codegen.IRCommon.Ty

import Native.Types.Enc as Types
import Native.Types.Kind

%default total

||| The pinned registers.
public export
data Pinned
  = ||| The allocation pointer.
    Hp
  | ||| The allocation limit.
    HpLim
  | ||| The current continuation: the collector's first root, which it
    ||| rewrites when it moves the continuation.
    K

public export
Show Pinned where
  show Hp = "Hp"
  show HpLim = "HpLim"
  show K = "K"

||| What a pinned register holds: a word for the window's, the continuation
||| for `K`.
public export
pinnedTy : Pinned -> Ty enc
pinnedTy Hp = Ty.W64
pinnedTy HpLim = Ty.W64
pinnedTy K = Ty.PtrTo Types.Kind.CONT
