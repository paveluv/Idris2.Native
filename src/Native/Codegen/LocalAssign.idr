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

import Native.Rep
import Native.Types.Enc as Types

%default total

-- where the row wants a location: in a register, if it is a slot of a
-- value of the register's class
wanted : Row.Want -> LocatedIR.Location enc t -> Maybe (LocatedIR.Location enc t)
wanted (Row.InRegister c k) l@(LocatedIR.Location.Slot _ t) =
  if IRCommon.Ty.class t == c then Just (LocatedIR.Location.inRegister k l) else Nothing
wanted _ _ = Nothing

-- an operand where the next want puts it, after the move that puts it
-- there; the wants run out wanting anywhere
operand : (List Row.Want, SnocList (LocatedIR.Instr enc)) -> LocatedIR.Location enc t ->
          ((List Row.Want, SnocList (LocatedIR.Instr enc)), LocatedIR.Location enc t)
operand ([], ms) l = (([], ms), l)
operand (w :: ws, ms) l = case wanted w l of
  Just g => ((ws, ms :< LocatedIR.Instr.Move g l), g)
  Nothing => ((ws, ms), l)

-- a result where the next want puts it, before the move that takes it to
-- its place
result : (List Row.Want, SnocList (LocatedIR.Instr enc)) -> LocatedIR.Location enc t ->
         ((List Row.Want, SnocList (LocatedIR.Instr enc)), LocatedIR.Location enc t)
result ([], ms) l = (([], ms), l)
result (w :: ws, ms) l = case wanted w l of
  Just g => ((ws, ms :< LocatedIR.Instr.Move l g), g)
  Nothing => ((ws, ms), l)

||| The instruction with its operands and results where its row wants them,
||| after the moves that put the operands there and before those that take
||| the results to their slots.
assigned : Row -> LocatedIR.Instr enc -> List (LocatedIR.Instr enc)
assigned r i =
  let ((_, before), i1) = LocatedIR.Instr.traverseOperands operand (r.operands, [<]) i
      ((_, after), i2) = LocatedIR.Instr.traverseResults result (r.results, [<]) i1
  in before <>> i2 :: (after <>> [])

||| The block with its instructions' and its terminator's operands and
||| results where the rows want them, its parallel moves made moves
||| through the registers of `temp`.
block : (row : LocatedIR.Instr enc -> Row) -> (termRow : LocatedIR.Terminator enc -> Row) ->
        (temp : Rep.RegClass -> Nat) -> LocatedIR.Block enc -> LocatedIR.Block enc
block row termRow temp b =
  let ((_, before), term) =
        LocatedIR.Terminator.traverseTermOperands operand ((termRow b.term).operands, [<]) b.term
  in { body := concatMap instr b.body ++ (before <>> []), term := term } b
  where
    instr : LocatedIR.Instr enc -> List (LocatedIR.Instr enc)
    instr (LocatedIR.Instr.Par cs) =
      concatMap (\m => assigned (row m) m) (Sequentialise.sequential temp cs)
    instr i = assigned (row i) i

||| Every instruction and terminator of the program with its operands and
||| results where `row` and `termRow` want them, a parallel move's cycle
||| broken through the register of `temp`.
export
localAssign : (row : LocatedIR.Instr enc -> Row) -> (termRow : LocatedIR.Terminator enc -> Row) ->
              (temp : Rep.RegClass -> Nat) -> LocatedIR.Program enc -> LocatedIR.Program enc
localAssign row termRow temp p =
  { functions $= map (\f => { blocks $= map (block row termRow temp) } f) } p
