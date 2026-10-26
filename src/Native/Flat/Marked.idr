||| The flat functions a program marks, and their flat forms; and the
||| constants it marks static.
|||
||| A program marks a function flat with a directive of the native code
||| generator, which Idris keeps with the module and passes on to every
||| module that imports it:
|||
|||     %cg native flat sumTo Main.classify
|||
||| and a constant static, which the native code generator evaluates as it
||| compiles the program (`Native.Codegen.Native` says what of it), with
||| another:
|||
|||     %cg native static Main.squares
|||
||| Each name is written as in the program, qualified as far as it takes to
||| name one definition. The backend's primitives (`Native.Primitive` says what
||| they are) are the code generator's to name, by their types: a call of one
||| is the primitive's, and its form applies it. The translation
||| (`Flat.Translate`) runs twice: as each module is built, by the incremental
||| code generator `flat-check`, which reports a function that is not flat as
||| an error of the module, at the term at fault; and when a program is
||| compiled, which makes the forms, and reports what no module's check did.
module Native.Flat.Marked

import Native.Flat.Exp
import Native.Flat.Problem
import Native.Flat.Report
import Native.Flat.Translate

import Compiler.Common
import Core.Binary
import Core.Binary.Prims
import Core.Context
import Core.Context.Context
import Core.Core
import Core.Directory
import Core.FC
import Core.Name
import Core.Name.Namespace
import Core.Options
import Core.TTC
import Core.UnifyState
import Data.List
import Data.Maybe
import Data.Zippable
import Idris.Error
import Idris.Pretty
import Idris.REPL.Opts
import Idris.Syntax
import Idris.Syntax.TTC
import Libraries.Data.NameMap
import Libraries.Text.PrettyPrint.Prettyprinter.Doc
import Libraries.Text.PrettyPrint.Prettyprinter.Render.String
import Libraries.Utils.Binary
import System.File

%default covering

||| The code generator whose directives mark flat functions and static
||| constants.
export
markingCG : CG
markingCG = Other "native"

||| Report the errors, in the order of the source, as one error of Idris's:
||| at the last error's location, with every error in its text as Idris
||| prints one, without colour. A code generator sees neither the REPL's
||| options nor its output mode, so it cannot print the errors itself: what
||| it printed would be text in the middle of the IDE protocol. Thrown, the
||| one error is shown as the mode asks.
report : {auto c : Ref Ctxt Defs} -> {auto s : Ref Syn SyntaxInfo} -> List Problem.FlatError ->
         Core ()
report errs
    = do o <- newRef ROpts ({ color := False, consoleWidth := Just 0 }
                              (defaultOpts Nothing (REPL ErrorLvl) []))
         es <- traverse Report.asError (sortBy (\a, b => compare (place a) (place b)) errs)
         case reverse es of
              [] => pure ()
              (e :: earlier) =>
                do texts <- traverse rendered (numbered (reverse earlier))
                   let (fc, msg) = errorMessage e
                   throw
                     (GenericMsg fc
                      (fastConcat (map (++ "\n") texts) ++ prefixed (length earlier) msg))
  where
    numbered : List a -> List (Nat, a)
    numbered xs = zip [0 .. length xs] xs

    -- Idris prefixes the whole with "Error:", so only the errors after the
    -- first carry their own.
    prefixed : Nat -> String -> String
    prefixed Z msg = msg
    prefixed _ msg = "Error: " ++ msg

    errorMessage : Error -> (FC, String)
    errorMessage (GenericMsg fc msg) = (fc, msg)
    errorMessage e = (fromMaybe EmptyFC (getErrorLoc e), show e)
    -- The text of the file the error is in, for the excerpt Idris shows, if
    -- the file is found.
    errorSource : Error -> Core String
    errorSource e
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
        = do setCurrentElabSource !(errorSource e)
             doc <- if i == 0 then perror e else display e
             pure (renderString (layoutPretty (MkLayoutOptions Unbounded) doc))

    -- Where an error is, to report errors in the order of the source.
    place : Problem.FlatError -> (Int, Int)
    place (Problem.UnknownMarkedName _ _ _) = (0, 0)
    place (Problem.NotFlat fc _ _ _ _) = maybe (0, 0) startPos (isNonEmptyFC fc)
    place (Problem.NotFlatBody fc _ _ _) = maybe (0, 0) startPos (isNonEmptyFC fc)

-- The session directive that records that a module's check (`checkModule`)
-- has reported errors in this run of the compiler.
reportedMark : String
reportedMark = "flat-errors-reported"

||| What a program's directives mark (`markedForms`): the flat forms of the
||| functions marked flat and of the ground functions they call, the
||| functions marked flat, and the constants marked static, each a
||| definition's full name.
public export
record Marked where
  constructor MkMarked
  forms : NameMap Exp.FlatDef
  flatFunctions : List Name
  staticConstants : List Name

||| What the program marks: the flat forms of the functions it marks flat,
||| and of the ground functions they call, and the constants it marks
||| static. Any function marked flat that cannot be in the flat regime is an
||| error, as is a name either directive gives that names no one
||| definition, and every such error is reported. Idris compiles a program
||| after a module of it failed to build, so errors that a module's check
||| has reported already are not reported again: there are no forms then,
||| `Nothing`, and the program is not compiled.
|||
||| `load` brings in modules the program does not import, such as the
||| runtime's, whose directives mark definitions too. The program's marks
||| are resolved before it, so that a name the program gives cannot become
||| ambiguous with one of theirs.
export
markedForms : {auto c : Ref Ctxt Defs} -> {auto s : Ref Syn SyntaxInfo} ->
              (primitives : Ref Ctxt Defs -> Core (List Name)) -> (load : Core ()) ->
              Core (Maybe Marked)
markedForms primitives load
    = do own <- getDirectives markingCG
         flatOwn <- Translate.markedNames Problem.FlatMark own
         staticOwn <- Translate.markedNames Problem.StaticMark own
         load
         let theirs = filter (\d => not (elem d own)) !(getDirectives markingCG)
         flatTheirs <- Translate.markedNames Problem.FlatMark theirs
         staticTheirs <- Translate.markedNames Problem.StaticMark theirs
         prims <- primitives c
         let flat = fst flatOwn ++ fst flatTheirs
         (forms, errs) <- Translate.flatForms prims (flat ++ prims)
         let nameErrs = snd flatOwn ++ snd flatTheirs ++ snd staticOwn ++ snd staticTheirs
         session <- getSession
         if not (null errs) && elem reportedMark session.directives
            then pure Nothing
            else do report (nameErrs ++ errs)
                    pure (Just (MkMarked forms flat (nub (fst staticOwn ++ fst staticTheirs))))

||| Check the flat functions a module defines, as it is built, before its TTC
||| is written: what `flat-check` does as an incremental code generator
||| (`codegenFlatCheck`). The module's definitions still carry the locations of
||| their terms then, which the TTC drops, so an error in a body points at
||| the term, as an error of the module's own. A name a directive gives that
||| names no function, or more than one, is left to the compilation of a
||| program, since a directive does not say which module wrote it.
|||
||| A flat function's body reaches the bodies of what it calls, in other
||| modules, and theirs in turn, which name modules the checked one does not
||| import. Idris builds a module with its imports loaded but not theirs, but
||| for those re-exported, so the check loads every module the module imports
||| transitively first (`loadAll`), as a program's compilation does, and puts
||| back after it what the TTC is written from: the module's imports, its
||| hints to save, its directives and its namespace (`Defs` but its
||| context). The definitions it loaded stay in the context until Idris
||| clears it for the next module. The backend's primitives are found after
||| the loading, as a module loaded may define one (`Mul128`): before it, a
||| primitive's meaning-body would be translated for it. So a module imports
||| only what it uses.
|||
||| A module that defines no flat function has nothing to check, and the
||| check loads nothing for it: most modules, and every module of a program
||| that marks none.
export
checkModule : {auto c : Ref Ctxt Defs} -> {auto s : Ref Syn SyntaxInfo} ->
              (primitives : Ref Ctxt Defs -> Core (List Name)) -> (sourceFile : String) -> Core ()
checkModule primitives sourceFile
    = do here <- ctxtPathToNS sourceFile
         marked <- Translate.markedNames Problem.FlatMark !(getDirectives markingCG)
         mine <- filterM (definedIn here) (fst marked)
         if null mine then pure () else do
           before <- get Ctxt
           loadAll before
           -- the backend's primitives, those of the modules loaded too
           prims <- primitives c
           (_, errs) <- Translate.flatForms prims mine
           loaded <- get Ctxt
           put Ctxt ({ gamma := loaded.gamma } before)
           unless (null errs) $ setSession ({ directives $= (reportedMark ::) } !getSession)
           report errs
  where
    ||| The modules a module's TTC says it imports, each with whether it
    ||| re-exports it and the namespace it imports it as: read from the TTC's
    ||| start, as Idris's `readTTCFile` reads it, and as it reads it only in
    ||| full for a module not yet loaded. The fields before the imports are
    ||| the pinned Idris's TTC's, in its order.
    |||
    ||| Each field is read by a function of its own type: Idris finds a `TTC`
    ||| instance slowly, the more so for a type it must infer from the
    ||| statements around the read, as for `the (Core T) fromBuf` in a `do`
    ||| block, which took four times as long.
    importsIn : String -> Core (List (ModuleIdent, Namespace))
    importsIn fname
        = do Right buffer <- coreLift (readFromFile fname)
               | Left _ => pure []
             b <- newRef Bin buffer
             catch (do ignore (getHashes fname b)
                       ignore importHashes
                       ignore incData
                       ims <- importEntries
                       pure (map (\(m, _, as) => (m, as)) ims))
                   (\_ => pure [])
      where
        importHashes : Ref Bin Binary => Core (List (Namespace, Int))
        importHashes = fromBuf

        incData : Ref Bin Binary => Core (List (CG, String, List String))
        incData = fromBuf

        importEntries : Ref Bin Binary => Core (List (ModuleIdent, Bool, Namespace))
        importEntries = fromBuf

    ||| Every module the module imports, and theirs, loaded, as a program's
    ||| compilation loads them: the import graph walked from the module's
    ||| imports, each module's own read from its TTC (`importsIn`), and each
    ||| module not yet loaded read in (`readFromTTC`), as an import that is
    ||| not visible. A module loaded already is not read in again, which
    ||| would add its definitions twice. `Defs` but the context is put back
    ||| after.
    loadAll : Defs -> Core ()
    loadAll defs
        = do u <- newRef UST initUState
             go [] [ (m, as) | (m, _, as) <- imported defs ]
      where
        go : {auto u : Ref UST UState} -> (seen : List ModuleIdent) ->
             List (ModuleIdent, Namespace) -> Core ()
        go seen [] = pure ()
        go seen ((m, as) :: ms)
            = if m `elem` seen then go seen ms else do
                Right fname <- nsToPath EmptyFC m
                  | Left _ => go (m :: seen) ms
                loaded <- get Ctxt
                unless (m `elem` map (fst . snd) (allImported loaded)) $
                  ignore (readFromTTC {extra = SyntaxInfo} False EmptyFC False fname m as)
                more <- importsIn fname
                go (m :: seen) (more ++ ms)

    definedIn : ModuleIdent -> Name -> Core Bool
    definedIn here n
        = do defs <- get Ctxt
             Just gdef <- lookupCtxtExact n (gamma defs)
               | Nothing => pure False
             pure $ case isNonEmptyFC (location gdef) of
                         Just (PhysicalIdrSrc ident, _, _) => ident == here
                         _ => False
