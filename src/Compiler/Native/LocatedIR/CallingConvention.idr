||| A function's calling convention (`CallingConvention`).
|||
||| Part of the located IR (`Compiler.Native.LocatedIR.Program` says what it
||| is).
module Compiler.Native.LocatedIR.CallingConvention

%default total

||| A function's calling convention, as the term's (`Compiler.Native.TermIR.Conv`)
||| makes it.
public export
data CallingConvention
  = ||| Compiled Idris code, and the runtime routines that transfer control
    ||| into Idris code. A CPS function never executes a machine return:
    ||| control leaves it only by jumps. `Return`, `Call`, `TailCall`, `Apply`
    ||| and `TailApply` are allowed only here, and a `Call` or `TailCall`
    ||| targets a CPS function. A CPS function reaches `Direct` code only by
    ||| `DirectCall`.
    CPS
  | ||| Conventional machine call and return: the collector, the allocation
    ||| slow path, primitives. Only a Direct function ends in `Ret`, and only
    ||| a Direct function is the target of a `DirectCall`. It reaches CPS code
    ||| only by `Enter`, inside the runtime's `enterIdris` wrapper. The
    ||| collector must be Direct: as CPS code it would allocate continuations
    ||| in the space it is collecting.
    Direct

public export
Eq CallingConvention where
  CPS == CPS = True
  Direct == Direct = True
  _ == _ = False

public export
Show CallingConvention where
  show CPS = "CPS"
  show Direct = "Direct"
