||| The flat regime's errors (`Flat.Problem`) as Idris reports an error of
||| its own: the message, rendered as the REPL renders one.
module Flat.Report

import Core.Context
import Core.Core
import Core.Env
import Core.TT

import public Flat.Problem

import Idris.Pretty
import Idris.Resugar
import Idris.Syntax

import Data.String

import Libraries.Text.PrettyPrint.Prettyprinter
import Libraries.Text.PrettyPrint.Prettyprinter.Render.String

%default covering


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
