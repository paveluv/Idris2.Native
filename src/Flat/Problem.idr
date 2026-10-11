||| What keeps a function out of the flat regime: the reasons a type is not
||| flat, the problems the translation of a body meets, and the errors that
||| report them, rendered as Idris renders its own.
module Flat.Problem

import Core.Context
import Core.Core
import Core.Env
import Core.TT

import Idris.Pretty
import Idris.Resugar
import Idris.Syntax

import Data.String

import Libraries.Text.PrettyPrint.Prettyprinter
import Libraries.Text.PrettyPrint.Prettyprinter.Render.String

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

------------------------------------------------------------------------------
-- Rendering

term : {auto c : Ref Ctxt Defs} -> {auto s : Ref Syn SyntaxInfo} -> ClosedTerm -> Core (Doc IdrisAnn)
term tm
    = do defs <- get Ctxt
         itm <- resugar Env.empty !(normaliseHoles defs Env.empty tm)
         pure (prettyBy Syntax itm)

name : {auto c : Ref Ctxt Defs} -> Name -> Core (Doc IdrisAnn)
name n = pure (code (pretty0 !(prettyName !(toFullNames n))))

-- The position of a flat function's argument, or its result.
argDoc : Maybe (Nat, Name) -> Doc IdrisAnn
argDoc Nothing = reflow "its result"
argDoc (Just (i, x))
    = if isUserName x then reflow "its argument" <++> code (pretty0 x)
         else reflow "its argument number" <++> byShow i

fieldDoc : Name -> Doc IdrisAnn
fieldDoc f = if isUserName f then reflow "the field" <++> code (pretty0 f) else reflow "a field"

reasonDoc : {auto c : Ref Ctxt Defs} -> {auto s : Ref Syn SyntaxInfo} ->
            NotFlatReason -> Core (Doc IdrisAnn)
reasonDoc (BoxedPrimitive IntegerType)
    = pure (reflow "an" <++> code "Integer" <++> reflow "may need the heap")
reasonDoc (BoxedPrimitive pt) = pure (code (byShow pt) <++> reflow "lives on the heap")
reasonDoc (NaturalType t)
    = pure (!(name t) <++> reflow "is an" <++> code "Integer" <++> reflow "at run time")
reasonDoc RuntimeType = pure (reflow "a type at run time is not flat")
reasonDoc FunctionType = pure (reflow "a function is not flat")
reasonDoc LazyType = pure (reflow "a lazy value is not flat")
reasonDoc (RecursiveType t) = pure (!(name t) <++> reflow "is recursive")
reasonDoc (ExternalType t) = pure (!(name t) <++> reflow "is an external type")
reasonDoc StuckType = pure (reflow "the type does not reduce to one that can be judged")
reasonDoc (UndeterminedField c f)
    = pure (reflow "the type of" <++> fieldDoc f <++> reflow "of" <++> !(name c)
              <++> reflow "is not determined by the type's arguments")
reasonDoc (InField c f fty w)
    = pure (fieldDoc f <++> reflow "of" <++> !(name c) <++> reflow "has type"
              <++> code !(term fty) <+> comma <++> reflow "and" <++> !(reasonDoc w))
reasonDoc (InFunction pos ty w)
    = pure (reflow "the function's" <++> position pos <++> reflow "has type"
              <++> code !(term ty) <+> comma <++> reflow "and" <++> !(reasonDoc w))
  where
    position : Maybe (Nat, Name) -> Doc IdrisAnn
    position Nothing = reflow "result"
    position (Just (i, x))
        = if isUserName x then reflow "argument" <++> code (pretty0 x)
             else reflow "argument number" <++> byShow i

problemDoc : {auto c : Ref Ctxt Defs} -> {auto s : Ref Syn SyntaxInfo} ->
             FlatProblem -> Core (Doc IdrisAnn)
problemDoc (ValueNotFlat ty why)
    = pure (reflow "it has a value of type" <++> code !(term ty) <+> colon <++> !(reasonDoc why))
problemDoc NotStatic
    = pure (reflow "it uses a function or a lazy value other than by applying or forcing it")
problemDoc (CalleeNotFlat g arg ty why)
    = pure (reflow "it calls" <++> !(name g) <+> comma <++> reflow "and" <++> argDoc arg
              <++> reflow "has type" <++> code !(term ty) <+> colon <++> !(reasonDoc why))
problemDoc (PrivateElsewhere g)
    = pure (reflow "it uses the private primitive" <++> !(name g) <++> reflow "outside its module")
problemDoc (CopiesDoNotEnd g)
    = pure (reflow "its calls of" <++> !(name g)
              <++> reflow "at static arguments grow without end, each needing a copy of its own")
problemDoc (Unhandled what) = pure (reflow what <++> reflow "is not handled in the flat regime")

message : FC -> Doc IdrisAnn -> Core Error
message fc doc = pure (GenericMsg fc (renderString (layoutPretty (MkLayoutOptions Unbounded) doc)))

||| The error, as Idris reports an error of its own: where, and the message.
export
asError : {auto c : Ref Ctxt Defs} -> {auto s : Ref Syn SyntaxInfo} -> FlatError -> Core Error
asError (UnknownFlatName str [])
    = pure (GenericMsg EmptyFC ("The flat directive names " ++ str ++ ", which is no function"))
asError (UnknownFlatName str ns)
    = pure (GenericMsg EmptyFC ("The flat directive names " ++ str ++ ", which is ambiguous: "
                                  ++ concat (intersperse ", " (map show ns))
                                  ++ ". Qualify it with its namespace."))
asError (NotFlat fc n arg ty why)
    = message fc (!(name n) <++> reflow "is flat, but" <++> argDoc arg <++> reflow "has type"
                    <++> code !(term ty) <+> colon <++> !(reasonDoc why) <+> dot)
asError (NotFlatBody fc n chain p)
    = do calls <- traverse call (runs chain)
         message fc (!(name n) <++> reflow "is flat, but" <++> hsep calls <++> !(problemDoc p) <+> dot)
  where
    -- The chain with each run of calls of one function as one entry, with
    -- how many calls deep it goes.
    runs : List Name -> List (Name, Nat)
    runs [] = []
    runs (g :: gs) = case runs gs of
                          ((h, k) :: rest) => if g == h then (g, S k) :: rest else (g, 1) :: (h, k) :: rest
                          [] => [(g, 1)]

    call : (Name, Nat) -> Core (Doc IdrisAnn)
    call (g, 1) = pure (reflow "it calls" <++> !(name g) <+> comma <++> reflow "and")
    call (g, k) = pure (reflow "it calls" <++> !(name g) <+> comma <++> reflow "nested" <++> byShow k
                          <++> reflow "deep, and")
