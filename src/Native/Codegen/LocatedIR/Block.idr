||| A basic block of the located IR (`Block`).
|||
||| Part of the located IR (`Native.Codegen.LocatedIR.Program` says what it
||| is).
module Native.Codegen.LocatedIR.Block

import Native.Codegen.LocatedIR.Content
import Native.Codegen.LocatedIR.Label
import Native.Codegen.LocatedIR.Location
import Native.Codegen.LocatedIR.Step
import Native.Codegen.LocatedIR.Terminator

import Data.List
import Native.Types.Enc as Types

%default total

||| A basic block. Only a resume block has parameters: its continuation's
||| `live` list followed by the result register. They declare what the block
||| receives; they do not define registers. Every other block reads the
||| registers set before it.
|||
||| Its certificate (`cert`) says what each location the block reads from
||| outside holds on its entry, its parameters' included: what register
||| allocation put there, which the allocation check holds to, at the
||| block's entry and at every jump or branch to it. Its terminator realises
||| the term's node of number `node`, as register allocation numbers the
||| term's definitions (`Step.Op`).
public export
record Block (enc : Types.Enc) where
  constructor MkBlock
  label : Label
  params : List (Location.Place enc)
  cert : List (Content, Location.Place enc)
  body : List (Step enc)
  term : Terminator enc
  node : Nat

||| A resume block's result register, the last of its parameters, where its
||| call's result arrives.
export
result : Block enc -> Maybe (Location.Place enc)
result b = last' b.params
