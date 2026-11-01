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
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Ty as IRCommon
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
  IfFixnums    : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} ->
    List (Location enc IRCommon.Ty.Val) ->
    (ifYes, ifNo : Label) ->
    Terminator enc
  ||| Compare and branch, with the operand types of `Cmp`. Renderings fuse
  ||| the comparison and the branch.
  Branch      : {0 t : IRCommon.Ty enc} -> IRCommon.Op.Rel -> Opnd enc t -> Opnd enc t ->
    (ifTrue, ifFalse : Label) -> Terminator enc
  ||| Branch on an integer to the block of the matching case, or else to the
  ||| default. The scrutinee is a `W64`, such as a constructor id from
  ||| `LoadPart`, or a `Fix`, whose cases are fixnums, as integers; the
  ||| rendering compares the words. The cases are distinct.
  Switch      : {0 t : IRCommon.Ty enc} -> Location enc t -> List (Int64, Label) ->
    (dflt : Label) ->
    Terminator enc
  ||| A non-tail call, CPS only: run the function, then continue at the
  ||| continuation's resume block, with its live registers and the result.
  Call        : Name -> List (Opnd.Arg enc) -> Cont enc -> Terminator enc
  ||| A tail call, CPS only: a transfer under the current continuation.
  TailCall    : Name -> List (Opnd.Arg enc) -> Terminator enc
  ||| A non-tail application of a closure to one argument, both `Val`s, CPS
  ||| only. It renders as a call to the runtime's apply routine.
  Apply       : (fn, arg : Location enc IRCommon.Ty.Val) -> Cont enc -> Terminator enc
  ||| A tail application, CPS only.
  TailApply   : (fn, arg : Location enc IRCommon.Ty.Val) -> Terminator enc
  ||| Deliver a `Val` to the current continuation, CPS only.
  Return      : Opnd enc IRCommon.Ty.Val -> Terminator enc
  ||| Jump to a code address held in a `W64`, with arguments, under the
  ||| current continuation. Allowed in both conventions; a `Direct`
  ||| function uses it only inside the runtime's `enterIdris` wrapper, the
  ||| one way from the runtime into Idris code.
  Enter       : Location enc IRCommon.Ty.CodeAddr -> List (Opnd enc IRCommon.Ty.Val) ->
    Terminator enc
  ||| A machine return, `Direct` only, with the function's results, which
  ||| match its `results` in number and type.
  Ret         : List (Opnd.Arg enc) -> Terminator enc
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

||| What a terminator reads, its register operands, in the order of its
||| fields: not the registers its continuation keeps.
export
termOperands : Terminator enc -> List (Location.Place enc)
termOperands t = case t of
  IfFixnums rs _ _ => map Location.At rs
  Branch _ x y _ _ => Opnd.opRegs x ++ Opnd.opRegs y
  Switch r _ _ => [Location.At r]
  Call _ args _ => Opnd.opsRegs args []
  TailCall _ args => Opnd.opsRegs args []
  Apply f x _ => [Location.At f, Location.At x]
  TailApply f x => [Location.At f, Location.At x]
  Return x => Opnd.opRegs x
  Enter f args => Location.At f :: concatMap Opnd.opRegs args
  Ret args => Opnd.opsRegs args []
  _ => []

public export
termCont : Terminator enc -> Maybe (Cont enc)
termCont (Call _ _ c) = Just c
termCont (Apply _ _ c) = Just c
termCont _ = Nothing

||| The registers the terminator names, its operands' and those its
||| continuation keeps live: each as often as it names it, in no order to
||| rely on.
export
termRegs : Terminator enc -> List (Location.Place enc)
termRegs t = termOperands t ++ maybe [] (.live) (termCont t)

||| The terminator with its register operands replaced by the step, in the
||| order `termOperands` lists them.
export
traverseTermOperands : Location.Step s enc -> s -> Terminator enc -> (s, Terminator enc)
traverseTermOperands f st t = case t of
  IfFixnums rs y n => let (s1, rs') = locs st rs in (s1, IfFixnums rs' y n)
  Branch r x y yes no =>
    let (s1, x') = Opnd.stepOpnd f st x
        (s2, y') = Opnd.stepOpnd f s1 y in (s2, Branch r x' y' yes no)
  Switch r cs d => let (s1, r') = f st r in (s1, Switch r' cs d)
  Call n args c => let (s1, args') = Opnd.stepArgs f st args in (s1, Call n args' c)
  TailCall n args => let (s1, args') = Opnd.stepArgs f st args in (s1, TailCall n args')
  Apply g x c => let (s1, g') = f st g; (s2, x') = f s1 x in (s2, Apply g' x' c)
  TailApply g x => let (s1, g') = f st g; (s2, x') = f s1 x in (s2, TailApply g' x')
  Return x => let (s1, x') = Opnd.stepOpnd f st x in (s1, Return x')
  Enter g args =>
    let (s1, g') = f st g; (s2, args') = opnds s1 args in (s2, Enter g' args')
  Ret args => let (s1, args') = Opnd.stepArgs f st args in (s1, Ret args')
  _ => (st, t)
  where
    locs : {0 u : IRCommon.Ty enc} -> s -> List (Location enc u) -> (s, List (Location enc u))
    locs st' [] = (st', [])
    locs st' (l :: ls) = let (s1, l') = f st' l; (s2, ls') = locs s1 ls in (s2, l' :: ls')

    opnds : {0 u : IRCommon.Ty enc} -> s -> List (Opnd enc u) -> (s, List (Opnd enc u))
    opnds st' [] = (st', [])
    opnds st' (o :: os) =
      let (s1, o') = Opnd.stepOpnd f st' o; (s2, os') = opnds s1 os in (s2, o' :: os')
