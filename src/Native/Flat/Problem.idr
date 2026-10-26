||| What keeps a function out of the flat regime: the reasons a type is not
||| flat, the problems the translation of a body meets, and the errors that
||| report them, with a name a marking directive gives that names no one
||| definition. `Flat.Report` renders them as Idris renders its own.
module Native.Flat.Problem

import Core.FC
import Core.Name
import Core.TT.Primitive
import Core.TT.Term

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

||| A directive of the native code generator that marks definitions by
||| name (`Flat.Marked`): `flat`, the functions the flat regime compiles, or
||| `static`, the constants the code generator computes as it compiles the
||| program.
public export
data Mark = FlatMark | StaticMark

||| The directive's first word, which the names it marks follow.
export
directive : Mark -> String
directive FlatMark = "flat"
directive StaticMark = "static"

||| Why a function marked flat cannot be in the flat regime, or why a name a
||| directive marks is no definition.
public export
data FlatError : Type where
  ||| A name a directive of the mark gives that names no definition, or
  ||| more than one: the name as written, and those it names.
  UnknownMarkedName : Mark -> String -> List Name -> FlatError
  ||| An argument (its position among the explicit arguments, from 1, and
  ||| its name) or the result (`Nothing`) of the function has a type that is
  ||| not flat.
  NotFlat : FC -> Name -> Maybe (Nat, Name) -> ClosedTerm -> NotFlatReason -> FlatError
  ||| The body of the function (`fn`), or of a function it calls through
  ||| `chain`, is not flat: the problem, at the location.
  NotFlatBody : FC -> (fn : Name) -> (chain : List Name) -> FlatProblem -> FlatError
