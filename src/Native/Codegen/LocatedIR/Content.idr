||| What a location holds (`Content`), as register allocation states it of a
||| block's entry (`Block.cert`) and the value check follows it.
|||
||| Part of the located IR (`Native.Codegen.LocatedIR.Program` says what it
||| is).
module Native.Codegen.LocatedIR.Content

import Native.Codegen.LocatedIR.Step

import Core.Name

%default total

||| The value of a definition of the term, by its number (`Step.Op`); or a
||| value register allocation put there (`Step.Materialised`).
public export
data Content = Value Nat | Put Step.Materialised

public export
Show Content where
  show (Value n) = "v" ++ show n
  show (Put m) = show m

||| Whether two contents are one value.
export
same : Content -> Content -> Bool
same (Value n) (Value m) = n == m
same (Put (Step.Immediate i)) (Put (Step.Immediate j)) = i == j
same (Put (Step.StaticAddress s)) (Put (Step.StaticAddress t)) = s == t
same _ _ = False
