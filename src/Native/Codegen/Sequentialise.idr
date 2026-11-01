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
import Native.Codegen.LocatedIR.Instr as LocatedIR
import Native.Codegen.LocatedIR.Location as LocatedIR

import Native.Rep
import Native.Types.Enc as Types

%default total

||| The moves of the parallel move, one at a time; `temp` the index of the
||| register of each class a cycle is broken through.
export
sequential : (temp : Rep.RegClass -> Nat) ->
             List (LocatedIR.Location enc, LocatedIR.Location enc) -> List (LocatedIR.Instr enc)
sequential temp ms =
  let moves = filter (\(d, x) => not (LocatedIR.Location.samePlace d x)) ms
  in steps (length moves) moves
  where
    -- whether a move of the list reads the place
    read : LocatedIR.Location enc -> List (LocatedIR.Location enc, LocatedIR.Location enc) -> Bool
    read p = any (\(_, x) => LocatedIR.Location.samePlace x p)

    -- the first move whose destination no move of the list reads, and the
    -- others
    free : List (LocatedIR.Location enc, LocatedIR.Location enc) ->
           List (LocatedIR.Location enc, LocatedIR.Location enc) ->
           Maybe ((LocatedIR.Location enc, LocatedIR.Location enc),
                  List (LocatedIR.Location enc, LocatedIR.Location enc))
    free _ [] = Nothing
    free seen (m@(d, _) :: rest) =
      if read d seen || read d rest then free (m :: seen) rest
        else Just (m, reverse seen ++ rest)

    -- one move a step, so as many steps as moves
    steps : Nat -> List (LocatedIR.Location enc, LocatedIR.Location enc) ->
            List (LocatedIR.Instr enc)
    steps _ [] = []
    steps (S k) ms' = case free [] ms' of
      Just ((d, x), rest) => LocatedIR.Instr.Move d x :: steps k rest
      Nothing => case ms' of
        ((d, x) :: rest) =>
          let t = LocatedIR.Location.Register (temp (IRCommon.Ty.class (LocatedIR.Location.ty d)))
                    (LocatedIR.Location.ty d)
              rest' = map (\(d', x') => (d', if LocatedIR.Location.samePlace x' d then t else x'))
                        rest
          in LocatedIR.Instr.Move t d :: LocatedIR.Instr.Move d x :: steps k rest'
        [] => []
    -- not reached: each step takes one move
    steps Z ms' = map (\(d, x) => LocatedIR.Instr.Move d x) ms'
