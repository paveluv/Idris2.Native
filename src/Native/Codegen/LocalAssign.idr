||| Each instruction's operands and results put where its row wants them
||| (`localAssign`, `Native.Codegen.Row`): an operand in a slot that the
||| row wants in a register moved there just before the instruction; a
||| result the row wants in a register written there, and moved into its
||| slot just after. The rendering then finds them where it reads and
||| writes them. Today every value is in a slot of its own, so every value
||| an instruction reads is moved in and every value it makes moved out; a
||| register allocator keeps values in registers instead, and moves only
||| where a row and a value's place disagree. A parallel move, a jump's,
||| becomes moves first (`Native.Codegen.Sequentialise`), which the rows
||| then place as any other.
module Native.Codegen.LocalAssign

import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Codegen.LocatedIR.Block as LocatedIR
import Native.Codegen.LocatedIR.Function as LocatedIR
import Native.Codegen.LocatedIR.Instr as LocatedIR
import Native.Codegen.LocatedIR.Location as LocatedIR
import Native.Codegen.LocatedIR.Program as LocatedIR
import Native.Codegen.LocatedIR.Terminator as LocatedIR
import Native.Codegen.Row
import Native.Codegen.Sequentialise

import Data.List
import Data.Maybe
import Data.Zippable
import Native.Rep
import Native.Types.Enc as Types

%default total

-- where the row wants a location: in a register, if it is a slot of a
-- value of the register's class
wanted : Row.Want -> LocatedIR.Location enc -> Maybe (LocatedIR.Location enc)
wanted (Row.InRegister c k) (LocatedIR.Location.Slot _ t) =
  if IRCommon.Ty.class t == c then Just (LocatedIR.Location.Register k t) else Nothing
wanted _ _ = Nothing

-- each location with its want, the wants run out wanting anywhere
paired : List Row.Want -> List (LocatedIR.Location enc) -> List (Row.Want, LocatedIR.Location enc)
paired ws ls = zip (ws ++ replicate (length ls) Row.Anywhere) ls

||| The instruction with its operands and results where its row wants them,
||| after the moves that put the operands there and before those that take
||| the results to their slots.
assigned : Row -> LocatedIR.Instr enc -> List (LocatedIR.Instr enc)
assigned r i =
  let ins = map (\(w, l) => (l, wanted w l)) (paired r.operands (LocatedIR.Instr.operands i))
      outs = map (\(w, l) => (l, wanted w l)) (paired r.results (LocatedIR.Instr.results i))
      before = mapMaybe (\(l, m) => map (\g => LocatedIR.Instr.Move g l) m) ins
      after = mapMaybe (\(l, m) => map (\g => LocatedIR.Instr.Move l g) m) outs
      i' = LocatedIR.Instr.withResults (map (\(l, m) => fromMaybe l m) outs)
             (LocatedIR.Instr.withOperands (map (\(l, m) => fromMaybe l m) ins) i)
  in before ++ i' :: after

||| The block with its instructions' and its terminator's operands and
||| results where the rows want them, its parallel moves made moves
||| through the registers of `temp`.
block : (row : LocatedIR.Instr enc -> Row) -> (termRow : LocatedIR.Terminator enc -> Row) ->
        (temp : Rep.RegClass -> Nat) -> LocatedIR.Block enc -> LocatedIR.Block enc
block row termRow temp b =
  let r = termRow b.term
      ins =
        map (\(w, l) => (l, wanted w l))
          (paired r.operands (LocatedIR.Terminator.termOperands b.term))
      before = mapMaybe (\(l, m) => map (\g => LocatedIR.Instr.Move g l) m) ins
      term = LocatedIR.Terminator.withTermOperands (map (\(l, m) => fromMaybe l m) ins) b.term
  in { body := concatMap instr b.body ++ before, term := term } b
  where
    instr : LocatedIR.Instr enc -> List (LocatedIR.Instr enc)
    instr (LocatedIR.Instr.Par ms) =
      concatMap (\m => assigned (row m) m) (Sequentialise.sequential temp ms)
    instr i = assigned (row i) i

||| Every instruction and terminator of the program with its operands and
||| results where `row` and `termRow` want them, a parallel move's cycle
||| broken through the register of `temp`.
export
localAssign : (row : LocatedIR.Instr enc -> Row) -> (termRow : LocatedIR.Terminator enc -> Row) ->
              (temp : Rep.RegClass -> Nat) -> LocatedIR.Program enc -> LocatedIR.Program enc
localAssign row termRow temp p =
  { functions $= map (\f => { blocks $= map (block row termRow temp) } f) } p
