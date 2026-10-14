||| A function's calling convention (`Conv`).
|||
||| Part of the vocabulary the native backend's two IRs share
||| (`Compiler.Native.IRCommon.Ty` says what it is).
module Compiler.Native.IRCommon.Conv

import Compiler.Native.HeapObject.Enc
import Compiler.Native.IRCommon.Ty

%default total

||| A function's calling convention, the same in both IRs.
public export
data Conv : Enc -> Type where
  ||| Compiled Idris code, and the runtime routines that transfer control
  ||| into Idris code. A CPS function never executes a machine return:
  ||| control leaves it only by jumps. `Return`, `Call`, `TailCall`, `Apply`
  ||| and `TailApply` are allowed only here, and a `Call` or `TailCall`
  ||| targets a CPS function. A CPS function reaches `Direct` code only by
  ||| `DirectCall`.
  CPS : Conv enc
  ||| Conventional machine call and return: the collector, the allocation
  ||| slow path, primitives. Only a Direct function ends in `Ret`, and only
  ||| a Direct function is the target of a `DirectCall`. It reaches CPS code
  ||| only by `Enter`, inside the runtime's `enterIdris` wrapper. The
  ||| collector must be Direct: as CPS code it would allocate continuations
  ||| in the space it is collecting. A Direct function declares its results,
  ||| and whether a call of it may start a collection.
  Direct : (results : List (Ty enc)) -> (collects : Bool) -> Conv enc

public export
Eq (Conv enc) where
  CPS == CPS = True
  Direct rs c == Direct rs' c' = rs == rs' && c == c'
  _ == _ = False

public export
Show (Conv enc) where
  show CPS = "CPS"
  show (Direct _ _) = "Direct"

namespace Conv
  ||| The results a function of the convention returns by a machine return:
  ||| a Direct function's; a CPS function's one value goes to its
  ||| continuation instead.
  public export
  results : Conv enc -> List (Ty enc)
  results CPS = []
  results (Direct rs _) = rs
