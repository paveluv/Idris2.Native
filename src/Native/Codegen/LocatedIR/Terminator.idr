||| How a block of the located IR ends (`Terminator`).
|||
||| Part of the located IR (`Native.Codegen.LocatedIR.Program` says what it
||| is).
module Native.Codegen.LocatedIR.Terminator

import Native.Codegen.LocatedIR.Cont
import Native.Codegen.LocatedIR.Label
import Native.Codegen.LocatedIR.Location
import Native.Codegen.LocatedIR.Opnd

import Core.Name
import Data.List
import Data.Zippable
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
  IfFixnums    : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} -> List (Location enc) ->
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
  Switch      : Location enc -> List (Int64, Label) -> (dflt : Label) -> Terminator enc
  ||| A non-tail call, CPS only: run the function, then continue at the
  ||| continuation's resume block, with its live registers and the result.
  Call        : Name -> List (Opnd enc) -> Cont enc -> Terminator enc
  ||| A tail call, CPS only: a transfer under the current continuation.
  TailCall    : Name -> List (Opnd enc) -> Terminator enc
  ||| A non-tail application of a closure to one argument, both `Val`s, CPS
  ||| only. It renders as a call to the runtime's apply routine.
  Apply       : (fn, arg : Location enc) -> Cont enc -> Terminator enc
  ||| A tail application, CPS only.
  TailApply   : (fn, arg : Location enc) -> Terminator enc
  ||| Deliver a `Val` to the current continuation, CPS only.
  Return      : Opnd enc -> Terminator enc
  ||| Jump to a code address held in a `W64`, with arguments, under the
  ||| current continuation. Allowed in both conventions; a `Direct`
  ||| function uses it only inside the runtime's `enterIdris` wrapper, the
  ||| one way from the runtime into Idris code.
  Enter       : Location enc -> List (Opnd enc) -> Terminator enc
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

||| The registers the terminator names, its operands' and those its
||| continuation keeps live: each as often as it names it, in no order to
||| rely on.
export
termRegs : Terminator enc -> List (Location enc)
termRegs t = case t of
  Jump _ => []
  IfFixnums rs _ _ => rs
  Branch _ x y _ _ => Opnd.opRegs x ++ Opnd.opRegs y
  Switch r _ _ => [r]
  Call _ args c => Opnd.opsRegs args c.live
  TailCall _ args => Opnd.opsRegs args []
  Apply f x c => f :: x :: c.live
  TailApply f x => [f, x]
  Return x => Opnd.opRegs x
  Enter f args => f :: Opnd.opsRegs args []
  Ret args => Opnd.opsRegs args []
  Crash _ => []
  Unsupported _ => []

public export
termCont : Terminator enc -> Maybe (Cont enc)
termCont (Call _ _ c) = Just c
termCont (Apply _ _ c) = Just c
termCont _ = Nothing

||| What a terminator reads, its register operands, in the order of its
||| fields: not the registers its continuation keeps.
export
termOperands : Terminator enc -> List (Location enc)
termOperands t = case t of
  IfFixnums rs _ _ => rs
  Branch _ x y _ _ => Opnd.opRegs x ++ Opnd.opRegs y
  Switch r _ _ => [r]
  Call _ args _ => Opnd.opsRegs args []
  TailCall _ args => Opnd.opsRegs args []
  Apply f x _ => [f, x]
  TailApply f x => [f, x]
  Return x => Opnd.opRegs x
  Enter f args => f :: Opnd.opsRegs args []
  Ret args => Opnd.opsRegs args []
  _ => []

||| The terminator with its register operands replaced, in the order
||| `termOperands` lists them, by as many locations; an operand the list has
||| no location for stays.
export
withTermOperands : List (Location enc) -> Terminator enc -> Terminator enc
withTermOperands rs t = case t of
  IfFixnums rs' y n => IfFixnums (zipWith const rs rs' ++ drop (length rs) rs') y n
  Branch r x y yes no => let (x', rs1) = opnd rs x; (y', _) = opnd rs1 y in Branch r x' y' yes no
  Switch r cs d => Switch (loc rs r) cs d
  Apply f x c => Apply (loc rs f) (loc (drop 1 rs) x) c
  TailApply f x => TailApply (loc rs f) (loc (drop 1 rs) x)
  Return x => Return (fst (opnd rs x))
  _ => t
  where
    loc : List (Location enc) -> Location enc -> Location enc
    loc (r :: _) _ = r
    loc [] x = x

    opnd : List (Location enc) -> Opnd enc -> (Opnd enc, List (Location enc))
    opnd (r :: rs') (Opnd.R _) = (Opnd.R r, rs')
    opnd rs' o = (o, rs')
