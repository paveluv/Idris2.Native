||| The flat functions a program marks, and their flat forms.
|||
||| A program marks a function flat with a directive of the native code
||| generator, which Idris keeps with the module and passes on to every
||| module that imports it:
|||
|||     %cg native flat sumTo Main.classify
|||
||| Each name is written as in the program, qualified as far as it takes to
||| name one function. The translation (`Flat.Translate`) runs twice: as each
||| module is built, by the incremental code generator `flat-check`, which
||| reports a function that is not flat as an error of the module, at the
||| term at fault; and when a program is compiled, which makes the forms, and
||| reports what no module's check did.
module Flat.Marked

import Core.Context
import Core.Core
import Core.Name

import Compiler.Common

import Core.Directory
import Core.FC

import public Flat.Exp
import Flat.Problem
import Flat.Translate

import Idris.Error
import Idris.Pretty
import Idris.REPL.Opts
import Idris.Syntax

import Data.List
import Data.Maybe

import Libraries.Text.PrettyPrint.Prettyprinter
import Libraries.Text.PrettyPrint.Prettyprinter.Render.String

import public Libraries.Data.NameMap

%default covering

||| The code generator whose directives mark flat functions.
export
markingCG : CG
markingCG = Other "native"

-- Where an error is, to report errors in the order of the source.
place : FlatError -> (Int, Int)
place (UnknownFlatName _ _) = (0, 0)
place (NotFlat fc _ _ _ _) = maybe (0, 0) startPos (isNonEmptyFC fc)
place (NotFlatBody fc _ _ _) = maybe (0, 0) startPos (isNonEmptyFC fc)

||| Report the errors, in the order of the source, as one error of Idris's:
||| at the last error's location, with every error in its text as Idris
||| prints one, without colour. A code generator sees neither the REPL's
||| options nor its output mode, so it cannot print the errors itself: what
||| it printed would be text in the middle of the IDE protocol. Thrown, the
||| one error is shown as the mode asks.
report : {auto c : Ref Ctxt Defs} -> {auto s : Ref Syn SyntaxInfo} -> List FlatError -> Core ()
report errs
    = do o <- newRef ROpts ({ color := False, consoleWidth := Just 0 }
                              (defaultOpts Nothing (REPL ErrorLvl) []))
         es <- traverse asError (sortBy (\a, b => compare (place a) (place b)) errs)
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
export
markedForms : {auto c : Ref Ctxt Defs} -> {auto s : Ref Syn SyntaxInfo} -> Core (Maybe (NameMap FlatDef))
markedForms
    = do marked <- flatNames !(getDirectives markingCG)
         (forms, errs) <- flatForms (fst marked)
         let nameErrs = snd marked
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
              (sourceFile : String) -> Core ()
checkModule sourceFile
    = do here <- ctxtPathToNS sourceFile
         marked <- flatNames !(getDirectives markingCG)
         mine <- filterM (definedIn here) (fst marked)
         (_, errs) <- flatForms mine
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

||| The code generator `flat-check`, which compiles nothing: as an incremental
||| code generator (`--inc flat-check`), it checks each module's flat
||| functions as the module is built (`checkModule`), and records the source
||| file as its data. It is not the native code generator, because Idris stops
||| treating the code generator in use as incremental as soon as an imported
||| module, such as the Prelude, was built without it, which would turn the
||| check off under `--cg native` and rebuild every module each time.
export
codegenFlatCheck : Codegen
codegenFlatCheck = MkCG compileExpr executeExpr (Just check) Nothing
  where
    nothing : Core a
    nothing = throw (GenericMsg EmptyFC "flat-check only checks modules as they are built; it compiles nothing")

    compileExpr : Ref Ctxt Defs -> Ref Syn SyntaxInfo -> String -> String -> ClosedTerm -> String -> Core (Maybe String)
    compileExpr _ _ _ _ _ _ = nothing

    executeExpr : Ref Ctxt Defs -> Ref Syn SyntaxInfo -> String -> ClosedTerm -> Core ()
    executeExpr _ _ _ _ = nothing

    check : Ref Ctxt Defs -> Ref Syn SyntaxInfo -> (sourceFile : String) -> Core (Maybe (String, List String))
    check c s sourceFile
        = do checkModule sourceFile
             pure (Just (sourceFile, []))
