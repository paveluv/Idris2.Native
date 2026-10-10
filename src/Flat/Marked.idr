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

||| The flat forms of the functions the program marks, and of the ground
||| functions they call. Any function marked that cannot be in the flat
||| regime is an error, and every such error is reported.
export
markedForms : {auto c : Ref Ctxt Defs} -> {auto s : Ref Syn SyntaxInfo} -> Core (NameMap FlatDef)
markedForms
    = do directives <- getDirectives markingCG
         marked <- flatNames directives
         (forms, errs) <- flatForms (fst marked)
         let nameErrs = snd marked
         report (nameErrs ++ errs)
         pure forms
