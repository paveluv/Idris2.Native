||| A continuation, as the located IR says it (`Cont`): where to resume, and
||| what is live there.
|||
||| Part of the located IR (`Native.Codegen.LocatedIR.Program` says what it
||| is).
module Native.Codegen.LocatedIR.Cont

import Native.Codegen.LocatedIR.Label
import Native.Codegen.LocatedIR.Reg

import Native.Types.Enc as Types

%default total

||| The whole of what the IR says about a continuation: where to resume, and
||| what is live there. The resume block's parameters are exactly `live`
||| followed by the result register. How the live values survive the call is
||| the rendering's business: under the heap lowering they become the fields
||| of a `CONT`, under the stack lowering slots of a frame.
public export
record Cont (enc : Types.Enc) where
  constructor MkCont
  resume : Label
  live : List (Reg enc)
