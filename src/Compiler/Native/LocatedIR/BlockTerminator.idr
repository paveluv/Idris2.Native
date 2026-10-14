||| How a block of the located IR ends (`BlockTerminator`).
|||
||| Part of the located IR (`Compiler.Native.LocatedIR.Program` says what it
||| is).
module Compiler.Native.LocatedIR.BlockTerminator

import Compiler.Native.HeapObject.Enc
import Compiler.Native.HeapObject.ValEnc
import Compiler.Native.IRCommon.Operators.Rel
import Compiler.Native.LocatedIR.BlockLabel
import Compiler.Native.LocatedIR.Cont
import Compiler.Native.LocatedIR.Operand
import Compiler.Native.LocatedIR.Reg
import Core.Name

%default total

||| How a block ends; every block ends in exactly one terminator. Which ones a
||| function may use depends on its convention (`CallingConvention`).
public export
data BlockTerminator : Enc -> Type where
  ||| Continue at the block.
  Jump        : BlockLabel -> BlockTerminator enc
  ||| Branch on whether every one of the `Val`s is a fixnum, that is, on their
  ||| fixnum tags; the yes branch may narrow them to `Fix`es. The renderings
  ||| test the tags of several at once.
  IsFixnum    : {auto 0 fx : HasFixnums enc.val} -> List (Reg enc) -> (ifYes, ifNo : BlockLabel) -> BlockTerminator enc
  ||| Compare and branch, with the operand types of `Cmp`. Renderings fuse
  ||| the comparison and the branch.
  Branch      : Rel -> Operand enc -> Operand enc -> (ifTrue, ifFalse : BlockLabel) -> BlockTerminator enc
  ||| Branch on an integer to the block of the matching case, or else to the
  ||| default. The scrutinee is a `W64`, such as a constructor id from
  ||| `LoadPart`, or a `Fix`, whose cases are fixnums, as integers; the
  ||| rendering compares the words. The cases are distinct.
  Switch      : Reg enc -> List (Int64, BlockLabel) -> (dflt : BlockLabel) -> BlockTerminator enc
  ||| A non-tail call, CPS only: run the function, then continue at the
  ||| continuation's resume block, with its live registers and the result.
  Call        : Name -> List (Operand enc) -> Cont enc -> BlockTerminator enc
  ||| A tail call, CPS only: a transfer under the current continuation.
  TailCall    : Name -> List (Operand enc) -> BlockTerminator enc
  ||| A non-tail application of a closure to one argument, both `Val`s, CPS
  ||| only. It renders as a call to the runtime's apply routine.
  Apply       : (fn, arg : Reg enc) -> Cont enc -> BlockTerminator enc
  ||| A tail application, CPS only.
  TailApply   : (fn, arg : Reg enc) -> BlockTerminator enc
  ||| Deliver a `Val` to the current continuation, CPS only.
  Return      : Operand enc -> BlockTerminator enc
  ||| Jump to a code address held in a `W64`, with arguments, under the
  ||| current continuation. Allowed in both conventions; a `Direct`
  ||| function uses it only inside the runtime's `enterIdris` wrapper, the
  ||| one way from the runtime into Idris code.
  Enter       : Reg enc -> List (Operand enc) -> BlockTerminator enc
  ||| A machine return, `Direct` only, with the function's results, which
  ||| match its `results` in number and type.
  Ret         : List (Operand enc) -> BlockTerminator enc
  ||| Write the message to standard error and exit with status 1. There is
  ||| no unwinding.
  Crash       : String -> BlockTerminator enc
  ||| Exit with the abort status instead, for a construct the backend does
  ||| not lower yet: how an incomplete backend still links.
  Unsupported : String -> BlockTerminator enc

public export
termName : BlockTerminator enc -> String
termName (Jump _) = "Jump"
termName (IsFixnum _ _ _) = "IsFixnum"
termName (Branch _ _ _ _ _) = "Branch"
termName (Switch _ _ _) = "Switch"
termName (Call f _ _) = "Call " ++ show f
termName (TailCall f _) = "TailCall " ++ show f
termName (Apply _ _ _) = "Apply"
termName (TailApply _ _) = "TailApply"
termName (Return _) = "Return"
termName (Enter _ _) = "Enter"
termName (Ret _) = "Ret"
termName (Crash _) = "Crash"
termName (Unsupported _) = "Unsupported"

public export
termCont : BlockTerminator enc -> Maybe (Cont enc)
termCont (Call _ _ c) = Just c
termCont (Apply _ _ c) = Just c
termCont _ = Nothing
