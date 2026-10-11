||| The flat functions a program marks, and their flat forms.
|||
||| A program marks a function flat with a directive of the native code
||| generator, which Idris keeps with the module and passes on to every
||| module that imports it:
|||
|||     %cg native flat sumTo Main.classify
|||
||| Each name is written as in the program, qualified as far as it takes to
||| name one function. The translation (`Flat.Translate`) runs when a program
||| is compiled, so a function that is not flat is reported then, not when its
||| module is checked.
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

import Idris.REPL.Common
import Idris.REPL.Opts
import Idris.Syntax

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

||| Report the errors as Idris reports its own, in the order of the source,
||| and stop at the last. A code generator does not see the options of the
||| REPL, so every error but the last, which Idris shows itself, is shown
||| without colour or line breaks.
report : {auto c : Ref Ctxt Defs} -> {auto s : Ref Syn SyntaxInfo} -> List FlatError -> Core ()
report [] = pure ()
report errs
    = do o <- newRef ROpts ({ color := False, consoleWidth := Just 0 }
                              (defaultOpts Nothing (REPL ErrorLvl) []))
         es <- traverse asError (sortBy (\a, b => compare (place a) (place b)) errs)
         go es
  where
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

    source : {auto o : Ref ROpts REPLOpts} -> Error -> Core ()
    source e = setCurrentElabSource !(sourceOf e)

    go : {auto o : Ref ROpts REPLOpts} -> List Error -> Core ()
    go [] = pure ()
    go [e] = throw e
    go (e :: es) = do source e; emitError e; go es

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
