||| A parallel move as moves one at a time (`sequential`): each destination
||| gets its source's value from before any destination of the parallel
||| move is written, as the located IR's `Par` says.
|||
||| A move of a place to itself is no move. Of the others, one whose
||| destination no other move reads goes first: nothing reads what it
||| overwrites. When none is left, since the destinations are distinct,
||| every move left is on a cycle, such as x and y swapped; one is broken
||| by keeping its destination's value in a register the target gives
||| (`temp`, by class), which every move reading that destination then
||| reads instead, and the move goes. Each step makes one move, so a
||| parallel move of n becomes at most n moves and one save a cycle. The
||| save's register is free: a parallel move is a jump's, between
||| instructions, where every value is in its slot, and its other moves
||| name no register.
module Native.Codegen.Sequentialise

import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Codegen.LocatedIR.Location as LocatedIR
import Native.Codegen.LocatedIR.Step as LocatedIR

import Native.Rep
import Native.Types.Enc as Types

%default total

||| The moves of the parallel move, one at a time; `temp` the index of the
||| register of each class a cycle is broken through.
export
sequential : (temp : Rep.RegClass -> Nat) -> List (LocatedIR.Step.Copy enc) ->
             List (LocatedIR.Step enc)
sequential temp cs =
  let moves = filter (\(LocatedIR.Step.MkCopy d x) => not (LocatedIR.Location.samePlace d x)) cs
  in steps (length moves) moves
  where
    -- whether a copy of the list reads the place
    read : LocatedIR.Location enc t -> List (LocatedIR.Step.Copy enc) -> Bool
    read p = any (\(LocatedIR.Step.MkCopy _ x) => LocatedIR.Location.samePlace x p)

    -- the first copy whose destination no copy of the list reads, and the
    -- others
    free : List (LocatedIR.Step.Copy enc) -> List (LocatedIR.Step.Copy enc) ->
           Maybe (LocatedIR.Step.Copy enc, List (LocatedIR.Step.Copy enc))
    free _ [] = Nothing
    free seen (c@(LocatedIR.Step.MkCopy d _) :: rest) =
      if read d seen || read d rest then free (c :: seen) rest
        else Just (c, reverse seen ++ rest)

    -- the register a cycle is broken through, at the location's type
    saved : LocatedIR.Location enc t -> LocatedIR.Location enc t
    saved l = LocatedIR.Location.inRegister (temp (IRCommon.Ty.class (LocatedIR.Location.ty l))) l

    -- a copy reading the place `d` reads the register it is saved in instead
    reread : LocatedIR.Location enc t -> LocatedIR.Step.Copy enc -> LocatedIR.Step.Copy enc
    reread d c@(LocatedIR.Step.MkCopy d' x') =
      if LocatedIR.Location.samePlace x' d then LocatedIR.Step.MkCopy d' (saved x') else c

    -- one copy a step, so as many steps as copies
    steps : Nat -> List (LocatedIR.Step.Copy enc) -> List (LocatedIR.Step enc)
    steps _ [] = []
    steps (S k) cs' = case free [] cs' of
      Just (LocatedIR.Step.MkCopy d x, rest) => LocatedIR.Step.Move d x :: steps k rest
      Nothing => case cs' of
        (LocatedIR.Step.MkCopy d x :: rest) =>
          LocatedIR.Step.Move (saved d) d :: LocatedIR.Step.Move d x
            :: steps k (map (reread d) rest)
        [] => []
    -- not reached: each step takes one copy
    steps Z cs' = map (\(LocatedIR.Step.MkCopy d x) => LocatedIR.Step.Move d x) cs'
