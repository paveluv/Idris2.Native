||| What keeps a function out of the flat regime: the reasons a type is not
||| flat, the problems the translation of a body meets, and the errors that
||| report them. `Flat.Report` renders them as Idris renders its own.
module Flat.Problem

import Core.FC
import Core.Name
import Core.TT

%default covering

||| Why a type is not flat: why some of its values need the heap, or have
||| no form in registers at all. Every argument and the result of a flat
||| function is asked it.
public export
data NotFlatReason : Type where
  ||| `Integer` or `String`
  BoxedPrimitive : PrimType -> NotFlatReason
  ||| a type of natural numbers (`%builtin Natural`), an `Integer` at run time
  NaturalType : Name -> NotFlatReason
  ||| a type, as a value at run time
  RuntimeType : NotFlatReason
  FunctionType : NotFlatReason
  LazyType : NotFlatReason
  RecursiveType : Name -> NotFlatReason
  ||| a type implemented outside Idris (`[external]`)
  ExternalType : Name -> NotFlatReason
  ||| a type that does not reduce to one that can be judged
  StuckType : NotFlatReason
  ||| a constructor's field whose type the type's arguments do not determine
  UndeterminedField : (con : Name) -> (field : Name) -> NotFlatReason
  ||| a constructor's field whose type is not flat
  InField : (con : Name) -> (field : Name) -> (fieldTy : ClosedTerm) ->
            NotFlatReason -> NotFlatReason
  ||| a function whose argument (its position among the explicit arguments
  ||| and its name) or result (`Nothing`) has a type that is not flat
  InFunction : Maybe (Nat, Name) -> (ty : ClosedTerm) -> NotFlatReason -> NotFlatReason

||| What makes the body of a flat function, or of a function it calls, not
||| flat: what its translation into the flat regime (`Flat.Translate`) meets.
public export
data FlatProblem : Type where
  ||| a value at run time whose type is not flat
  ValueNotFlat : ClosedTerm -> NotFlatReason -> FlatProblem
  ||| a function or a lazy value used other than by applying or forcing it
  NotStatic : FlatProblem
  ||| a call of a function whose argument (its position among the explicit
  ||| arguments and its name) or result (`Nothing`) is not flat
  CalleeNotFlat : Name -> Maybe (Nat, Name) -> ClosedTerm -> NotFlatReason -> FlatProblem
  ||| a private primitive used where its own module did not write it
  PrivateElsewhere : Name -> FlatProblem
  ||| calls of a function at static arguments that grow without end, each
  ||| needing a copy of its own
  CopiesDoNotEnd : Name -> FlatProblem
  ||| a construct the translation does not handle
  Unhandled : String -> FlatProblem

||| Why a function marked flat cannot be in the flat regime.
public export
data FlatError : Type where
  ||| A name the `flat` directive gives that names no function, or more
  ||| than one.
  UnknownFlatName : String -> List Name -> FlatError
  ||| An argument (its position among the explicit arguments, from 1, and
  ||| its name) or the result (`Nothing`) of the function has a type that is
  ||| not flat.
  NotFlat : FC -> Name -> Maybe (Nat, Name) -> ClosedTerm -> NotFlatReason -> FlatError
  ||| The body of the function (`fn`), or of a function it calls through
  ||| `chain`, is not flat: the problem, at the location.
  NotFlatBody : FC -> (fn : Name) -> (chain : List Name) -> FlatProblem -> FlatError
