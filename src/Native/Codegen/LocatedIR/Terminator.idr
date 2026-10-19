||| How a block of the located IR ends (`Terminator`).
|||
||| Part of the located IR (`Native.Codegen.LocatedIR.Program` says what it
||| is).
module Native.Codegen.LocatedIR.Terminator

import Native.Codegen.LocatedIR.Cont
import Native.Codegen.LocatedIR.Label
import Native.Codegen.LocatedIR.Opnd
import Native.Codegen.LocatedIR.Reg

import Core.Name
import Native.Codegen.IRCommon.Op
import Native.HeapObj.ValEnc
import Native.Types.Enc as Types

%default total

||| How a block ends; every block ends in exactly one terminator. Which ones a
||| function may use depends on its convention (`Conv`).
public export
data Terminator : Types.Enc -> Type where
  ||| Continue at the block.
  Jump        : Label -> Terminator enc
  ||| Branch on whether every one of the `Val`s is a fixnum, that is, on their
  ||| fixnum tags; the yes branch may narrow them to `Fix`es. The renderings
  ||| test the tags of several at once.
  IfFixnums    : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} -> List (Reg enc) ->
    (ifYes, ifNo : Label) ->
    Terminator enc
  ||| Compare and branch, with the operand types of `Cmp`. Renderings fuse
  ||| the comparison and the branch.
  Branch      : IRCommon.Op.Rel -> Opnd enc -> Opnd enc -> (ifTrue, ifFalse : Label) ->
    Terminator enc
  ||| Branch on an integer to the block of the matching case, or else to the
  ||| default. The scrutinee is a `W64`, such as a constructor id from
  ||| `LoadPart`, or a `Fix`, whose cases are fixnums, as integers; the
  ||| rendering compares the words. The cases are distinct.
  Switch      : Reg enc -> List (Int64, Label) -> (dflt : Label) -> Terminator enc
  ||| A non-tail call, CPS only: run the function, then continue at the
  ||| continuation's resume block, with its live registers and the result.
  Call        : Name -> List (Opnd enc) -> Cont enc -> Terminator enc
  ||| A tail call, CPS only: a transfer under the current continuation.
  TailCall    : Name -> List (Opnd enc) -> Terminator enc
  ||| A non-tail application of a closure to one argument, both `Val`s, CPS
  ||| only. It renders as a call to the runtime's apply routine.
  Apply       : (fn, arg : Reg enc) -> Cont enc -> Terminator enc
  ||| A tail application, CPS only.
  TailApply   : (fn, arg : Reg enc) -> Terminator enc
  ||| Deliver a `Val` to the current continuation, CPS only.
  Return      : Opnd enc -> Terminator enc
  ||| Jump to a code address held in a `W64`, with arguments, under the
  ||| current continuation. Allowed in both conventions; a `Direct`
  ||| function uses it only inside the runtime's `enterIdris` wrapper, the
  ||| one way from the runtime into Idris code.
  Enter       : Reg enc -> List (Opnd enc) -> Terminator enc
  ||| A machine return, `Direct` only, with the function's results, which
  ||| match its `results` in number and type.
  Ret         : List (Opnd enc) -> Terminator enc
  ||| Write the message to standard error and exit with status 1. There is
  ||| no unwinding.
  Crash       : String -> Terminator enc
  ||| Exit with the abort status instead, for a construct the backend does
  ||| not lower yet: how an incomplete backend still links.
  Unsupported : String -> Terminator enc

public export
termName : Terminator enc -> String
termName (Jump _) = "Jump"
termName (IfFixnums _ _ _) = "IfFixnums"
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
termCont : Terminator enc -> Maybe (Cont enc)
termCont (Call _ _ c) = Just c
termCont (Apply _ _ c) = Just c
termCont _ = Nothing
