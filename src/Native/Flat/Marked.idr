||| The flat functions a program marks, and their flat forms.
|||
||| A program marks a function flat with a directive of the native code
||| generator, which Idris keeps with the module and passes on to every
||| module that imports it:
|||
|||     %cg native flat sumTo Main.classify
|||
||| Each name is written as in the program, qualified as far as it takes to
||| name one function. The backend's primitives (`Native.Primitive` says
||| what they are) are the code generator's to name, by their types: a call
||| of one is the primitive's, and its form applies it. The translation (`Flat.Translate`) runs twice: as each
||| module is built, by the incremental code generator `flat-check`, which
||| reports a function that is not flat as an error of the module, at the
||| term at fault; and when a program is compiled, which makes the forms, and
||| reports what no module's check did.
module Native.Flat.Marked

import Native.Flat.Exp
import Native.Flat.Problem
import Native.Flat.Report
import Native.Flat.Translate

import Compiler.Common
import Core.Context
import Core.Context.Context
import Core.Core
import Core.Directory
import Core.FC
import Core.Name
import Core.Name.Namespace
import Core.Options
import Data.List
import Data.Maybe
import Data.Zippable
import Idris.Error
import Idris.Pretty
import Idris.REPL.Opts
import Idris.Syntax
import Libraries.Data.NameMap
import Libraries.Text.PrettyPrint.Prettyprinter.Doc
import Libraries.Text.PrettyPrint.Prettyprinter.Render.String

%default covering

||| The code generator whose directives mark flat functions.
export
markingCG : CG
markingCG = Other "native"

||| Report the errors, in the order of the source, as one error of Idris's:
||| at the last error's location, with every error in its text as Idris
||| prints one, without colour. A code generator sees neither the REPL's
||| options nor its output mode, so it cannot print the errors itself: what
||| it printed would be text in the middle of the IDE protocol. Thrown, the
||| one error is shown as the mode asks.
report : {auto c : Ref Ctxt Defs} -> {auto s : Ref Syn SyntaxInfo} -> List Problem.FlatError -> Core ()
report errs
    = do o <- newRef ROpts ({ color := False, consoleWidth := Just 0 }
                              (defaultOpts Nothing (REPL ErrorLvl) []))
         es <- traverse Report.asError (sortBy (\a, b => compare (place a) (place b)) errs)
         case reverse es of
              [] => pure ()
              (e :: earlier) =>
                do texts <- traverse rendered (numbered (reverse earlier))
                   let (fc, msg) = messageOf e
                   throw (GenericMsg fc (fastConcat (map (++ "\n") texts) ++ prefixed (length earlier) msg))
  where
    numbered : List a -> List (Nat, a)
    numbered xs = zip [0 .. length xs] xs

    -- Idris prefixes the whole with "Error:", so only the errors after the
    -- first carry their own.
    prefixed : Nat -> String -> String
    prefixed Z msg = msg
    prefixed _ msg = "Error: " ++ msg

    messageOf : Error -> (FC, String)
    messageOf (GenericMsg fc msg) = (fc, msg)
    messageOf e = (fromMaybe EmptyFC (getErrorLoc e), show e)
    -- The text of the file the error is in, for the excerpt Idris shows, if
    -- the file is found.
    sourceOf : Error -> Core String
    sourceOf e
        = case the (Maybe NonEmptyFC) (getErrorLoc e >>= isNonEmptyFC) of
               Just (PhysicalIdrSrc ident, _, _) =>
                 catch (do path <- nsToSource EmptyFC ident
                           readFile path)
                       (\_ => pure "")
               _ => pure ""

    -- An error as Idris prints one: its message, then where it is, with
    -- the source around.
    rendered : {auto o : Ref ROpts REPLOpts} -> (Nat, Error) -> Core String
    rendered (i, e)
        = do setCurrentElabSource !(sourceOf e)
             doc <- if i == 0 then perror e else display e
             pure (renderString (layoutPretty (MkLayoutOptions Unbounded) doc))

    -- Where an error is, to report errors in the order of the source.
    place : Problem.FlatError -> (Int, Int)
    place (Problem.UnknownFlatName _ _) = (0, 0)
    place (Problem.NotFlat fc _ _ _ _) = maybe (0, 0) startPos (isNonEmptyFC fc)
    place (Problem.NotFlatBody fc _ _ _) = maybe (0, 0) startPos (isNonEmptyFC fc)

-- The session directive that records that a module's check (`checkModule`)
-- has reported errors in this run of the compiler.
reportedMark : String
reportedMark = "flat-errors-reported"

||| The flat forms of the functions the program marks, and of the ground
||| functions they call. Any function marked that cannot be in the flat
||| regime is an error, and every such error is reported. Idris compiles a
||| program after a module of it failed to build, so errors that a module's
||| check has reported already are not reported again: there are no forms
||| then, `Nothing`, and the program is not compiled.
|||
||| `load` brings in modules the program does not import, such as the
||| runtime's, whose directives mark functions too. The program's marks are
||| resolved before it, so that a name the program gives cannot become
||| ambiguous with one of theirs.
export
markedForms : {auto c : Ref Ctxt Defs} -> {auto s : Ref Syn SyntaxInfo} ->
              (primitives : Ref Ctxt Defs -> Core (List Name)) -> (load : Core ()) -> Core (Maybe (NameMap Exp.FlatDef))
markedForms primitives load
    = do own <- getDirectives markingCG
         marked <- Translate.flatNames own
         load
         loaded <- Translate.flatNames (filter (\d => not (elem d own)) !(getDirectives markingCG))
         prims <- primitives c
         (forms, errs) <- Translate.flatForms prims (fst marked ++ fst loaded ++ prims)
         let nameErrs = snd marked ++ snd loaded
         session <- getSession
         if not (null errs) && elem reportedMark session.directives
            then pure Nothing
            else do report (nameErrs ++ errs)
                    pure (Just forms)

||| Check the flat functions a module defines, as it is built, before its TTC
||| is written: what `flat-check` does as an incremental code generator
||| (`codegenFlatCheck`). The module's definitions still carry the locations of
||| their terms then, which the TTC drops, so an error in a body points at
||| the term, as an error of the module's own. A name a directive gives that
||| names no function, or more than one, is left to the compilation of a
||| program, since a directive does not say which module wrote it.
export
checkModule : {auto c : Ref Ctxt Defs} -> {auto s : Ref Syn SyntaxInfo} ->
              (primitives : Ref Ctxt Defs -> Core (List Name)) -> (sourceFile : String) -> Core ()
checkModule primitives sourceFile
    = do here <- ctxtPathToNS sourceFile
         marked <- Translate.flatNames !(getDirectives markingCG)
         mine <- filterM (definedIn here) (fst marked)
         (_, errs) <- Translate.flatForms !(primitives c) mine
         unless (null errs) $ setSession ({ directives $= (reportedMark ::) } !getSession)
         report errs
  where
    definedIn : ModuleIdent -> Name -> Core Bool
    definedIn here n
        = do defs <- get Ctxt
             Just gdef <- lookupCtxtExact n (gamma defs)
               | Nothing => pure False
             pure $ case isNonEmptyFC (location gdef) of
                         Just (PhysicalIdrSrc ident, _, _) => ident == here
                         _ => False
