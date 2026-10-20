||| A refactoring (`Refactoring`): a change the linter makes to the code by
||| itself, one candidate at a time, and the run of one over a file to a
||| fixed point.
|||
||| A refactoring names its candidates in a file, those ready to go, in the
||| order to take them. Each is planned on the file as parsed, as a change
||| or as the reason it stays: the safety checks are the planner's, and a
||| candidate that is not safe is reported, never forced. The run makes one
||| change at a time, parses every file it touched again, and undoes a
||| change any of them no longer parses after; then it parses the file again
||| and asks for the candidates anew, until none is left. A dry run does the
||| same, printing each change, and puts every file back at the end: one
||| without a check moves each file it touches aside first and back at the
||| end, its times kept, so that its TTC is still taken for built from it;
||| one with a check has had the edited files built, so it writes them back,
||| newer than their TTCs. Only the Idris files a change touches are parsed
||| and checked again.
|||
||| Parsing is all the linter itself can ask of a change. A run may be given
||| a check besides, a command that type checks a file, and a change any
||| touched file fails it after is undone too: the type checker is the
||| judge of what a planner could only reason about. A check costs seconds,
||| so a refactoring whose changes the planner judges is run to its fixed
||| point first and checked once, on every file it touched; only when one
||| fails is everything put back and the run made again, a check after
||| each change. One whose changes only the type checker can judge
||| (`needsCheck`) is checked change by change from the start.
module Lint.Refactor.Refactoring

import Lint.Refactor.Change
import Lint.Refactor.Edit
import Lint.Refactor.Project
import Lint.Refactor.Span
import Lint.Refactor.Subject

import Core.WithData
import Data.IORef
import Data.List
import Data.List1
import Data.Maybe
import Data.SortedMap
import Data.String
import Idris.Syntax
import Libraries.Data.WithData
import Lint.Resolution
import Lint.Rules
import Lint.Source
import System
import System.Directory
import System.File.Error
import System.File.Meta
import System.File.ReadWrite

%default covering

||| One thing a refactoring may change: what it is about, for the report,
||| and its change, or why it stays as it is; and, for a change the planner
||| cannot judge, the one it would rather make (`preferred`), which only
||| the type checker can judge: with a check it is tried first, the change
||| made if it fails; without one it is never made.
public export
record Candidate where
  constructor MkCandidate
  label : String
  plan : Either String Change
  preferred : Maybe Change

||| A candidate with no preferred change.
export
candidate : (label : String) -> Either String Change -> Candidate
candidate l p = MkCandidate l p Nothing

||| What a declaration is called in a report: the names it defines, or,
||| for one that defines none, such as an implementation, where it is.
export
labelOf : Rules.Declared -> String
labelOf d = case d.defines of
  [] => "the declaration at line " ++ show (fst (Span.lineSpan d.decl.fc) + 1)
  ns => fastConcat (intersperse ", " ns)

||| A refactoring: its name, as the command line gives it, what it does, and
||| its candidates in a file. One that changes other files than the one it
||| looks at, a module's importers, is given every file of the run, parsed
||| afresh before each change (`wide`). One whose changes only the type
||| checker can judge, an import that may or may not be needed, runs only
||| with a check (`needsCheck`).
public export
record Refactoring where
  constructor MkRefactoring
  name : String
  summary : String
  wide : Bool
  needsCheck : Bool
  candidates : Project -> Subject -> List Candidate

||| A refactoring that looks at one file at a time, its changes judged by
||| what it knows.
export
fileRefactoring : (name, summary : String) -> (Subject -> List Candidate) -> Refactoring
fileRefactoring n s cs = MkRefactoring n s False False (\_ => cs)

||| What a run did to a file: the candidates changed, and those that stay,
||| each with why.
public export
record Report where
  constructor MkReport
  path : String
  changed : List String
  stays : List (String, String)

||| The files a change touches, as they were before it: `Nothing` for a file
||| it creates.
Saved : Type
Saved = SortedMap String (Maybe String)

||| A run to a fixed point: the candidates changed and those that stay,
||| what the files it touched were before it, and each change made with
||| what its files were before it, the latest first.
record Run where
  constructor MkRun
  changed : List String
  stays : List (String, String)
  saved : Saved
  made : List (String, Saved, Change)

||| Moves a file to another path, its times with it: the C library's
||| `rename`, which base does not offer.
%foreign "C:rename,libc 6"
prim__rename : String -> String -> PrimIO Int

||| The file moved to the path; whether it was.
moveFile : (from, to : String) -> IO Bool
moveFile from to = (== 0) <$> primIO (prim__rename from to)

||| `refactor`, with the files a dry run without a check has moved aside so
||| far, each with where it is (`aside`).
runWith : (aside : IORef (List (String, String))) -> (dryRun : Bool) -> (check : Maybe String) ->
          Refactoring -> (project : IO Project) -> (changed : IO ()) -> (path : String) ->
          IO Report
runWith aside dryRun check r project changedFiles path = case check of
  Just cmd => if r.needsCheck then loop True check [] [] empty [] >>= finish else checkedOnce cmd
  Nothing => loop False Nothing [] [] empty [] >>= finish
  where
    ||| Whether the run moves the files it touches aside: a dry run's without
    ||| a check, which builds none of them.
    moves : Bool
    moves = dryRun && isNothing check

    ||| The file moved aside if the run moves files and has not moved it yet:
    ||| whether it was moved now.
    moveAside : String -> IO Bool
    moveAside p = if not moves then pure False else do
      moved <- readIORef aside
      if isJust (lookup p moved) then pure False else do
        let to = p ++ "~lint"
        True <- moveFile p to
          | False => pure False
        modifyIORef aside ((p, to) ::)
        pure True

    -- the directory a file is in, and the directories down to it,
    -- made where they are missing
    directoryOf : String -> String
    directoryOf p = case reverse (List1.forget (split (== '/') p)) of
      (_ :: rest@(_ :: _)) => joinBy "/" (reverse rest)
      _ => "."

    createDirectories : String -> IO (Either FileError ())
    createDirectories d = do
      True <- not <$> exists d
        | False => pure (Right ())
      ignore (createDirectories (directoryOf d))
      createDir d

    restore : Saved -> IO ()
    restore saved = for_ (SortedMap.toList saved) $ \(p, old) => case old of
      Just t => do ignore (createDirectories (directoryOf p)); ignore (writeFile p t)
      Nothing => ignore (removeFile p)

    ||| A change as a dry run prints it: each edit, with the text it replaces.
    printChange : Saved -> Change -> IO ()
    printChange saved ch = do
      for_ ch.edits $ \(p, es) => do
        putStrLn ("  " ++ p)
        let old = fromMaybe "" (join (lookup p saved))
        for_ es $ \e => traverse_ (putStrLn . ("    " ++)) (Edit.describe old e)
      for_ ch.created $ \(p, _) => putStrLn ("  created " ++ p)
      for_ ch.removed $ \p => putStrLn ("  removed " ++ p)

    finish : Run -> IO Report
    finish run = do
      when dryRun $ do
        for_ (reverse run.made) $ \(label, before, ch) => do
          putStrLn (r.name ++ ": " ++ label)
          printChange before ch
        restore run.saved
        moved <- readIORef aside
        for_ moved $ \(p, at) => ignore (moveFile at p)
      pure (MkReport path (reverse run.changed) (reverse run.stays))

    withPath : String -> String -> String
    withPath p cmd = case break (== '{') (unpack cmd) of
      (before, '{' :: '}' :: after) => pack before ++ p ++ withPath p (pack after)
      (before, c :: after) => pack (before ++ [c]) ++ withPath p (pack after)
      (before, []) => pack before

    ||| The first of the files the check fails on, if any.
    failsOn : (cmd : String) -> List String -> IO (Maybe String)
    failsOn _ [] = pure Nothing
    failsOn cmd (p :: more) = do
      0 <- system (withPath p cmd)
        | _ => pure (Just p)
      failsOn cmd more

    ||| A change made: each file edited and each created, what each was kept,
    ||| and every touched file parsed, and checked if there is a check,
    ||| again; or, with everything put back, why it could not be made.
    makeChange : (check : Maybe String) -> Change -> IO (Either String Saved)
    makeChange check ch = do
      Right saved <- editAll empty ch.edits
        | Left (why, saved) => do restore saved; pure (Left why)
      Right created <- createAll saved ch.created
        | Left (why, created) => do restore created; pure (Left why)
      Right saved' <- removeAll created ch.removed
        | Left (why, saved') => do restore saved'; pure (Left why)
      Nothing <- unparsed (sources saved')
        | Just why => do restore saved'; pure (Left why)
      Nothing <- unchecked (sources saved')
        | Just why => do restore saved'; pure (Left why)
      pure (Right saved')
      where
        -- the Idris files a change touched, which are parsed and checked
        -- again: a package's list is not
        sources : Saved -> List String
        sources saved = filter (\p => isSuffixOf ".idr" p && not (p `elem` ch.removed)) (keys saved)

        -- the files removed, what each was kept to be put back
        removeAll : Saved -> List String -> IO (Either (String, Saved) Saved)
        removeAll saved [] = pure (Right saved)
        removeAll saved (p :: rest) = do
          Right old <- readFile p
            | Left e => pure (Left ("cannot read " ++ p ++ ": " ++ show e, saved))
          let saved' = insert p (Just old) saved
          movedNow <- moveAside p
          Right () <- the (IO (Either FileError ())) (if movedNow then pure (Right ()) else removeFile p)
            | Left e => pure (Left ("cannot remove " ++ p ++ ": " ++ show e, saved'))
          -- the directory too, if the file was its last; an undo makes it
          -- again
          ignore (removeDir (directoryOf p))
          removeAll saved' rest

        editAll : Saved -> List (String, List Edit) -> IO (Either (String, Saved) Saved)
        editAll saved [] = pure (Right saved)
        editAll saved ((p, es) :: rest) = do
          Right old <- readFile p
            | Left e => pure (Left ("cannot read " ++ p ++ ": " ++ show e, saved))
          let saved' = if isJust (lookup p saved) then saved else insert p (Just old) saved
          case Edit.apply es old of
            Nothing => pure (Left ("its edits to " ++ p ++ " overlap", saved'))
            Just new => do
              ignore (moveAside p)
              Right () <- writeFile p new
                | Left e => pure (Left ("cannot write " ++ p ++ ": " ++ show e, saved'))
              editAll saved' rest

        createAll : Saved -> List (String, String) -> IO (Either (String, Saved) Saved)
        createAll saved [] = pure (Right saved)
        createAll saved ((p, t) :: rest) = do
          True <- not <$> exists p
            | False => pure (Left ("it would overwrite " ++ p, saved))
          let saved' = insert p Nothing saved
          ignore (createDirectories (directoryOf p))
          Right () <- writeFile p t
            | Left e => pure (Left ("cannot write " ++ p ++ ": " ++ show e, saved'))
          createAll saved' rest

        unparsed : List String -> IO (Maybe String)
        unparsed [] = pure Nothing
        unparsed (p :: ps) = do
          r <- Source.parse p
          case r of
            Left e => pure (Just ("the change leaves " ++ p ++ " unparsed: " ++ e))
            Right _ => unparsed ps

        -- the first touched file the check fails on, if there is a check
        unchecked : List String -> IO (Maybe String)
        unchecked ps = case check of
          Nothing => pure Nothing
          Just cmd => map (\p => "the change leaves " ++ p ++ " not checking") <$> failsOn cmd ps

    ||| The run from where it is to a fixed point, each change checked by
    ||| `check`, if one is given. `checked` says that a check judges the run,
    ||| now or once it is over, so that a candidate's preferred change may be
    ||| made: under a check, the change made when it fails.
    loop : (checked : Bool) -> (check : Maybe String) -> List String -> List (String, String) ->
           Saved -> List (String, Saved, Change) -> IO Run
    loop checked check changed stays saved made = do
      -- a change of another file's may have removed this one
      True <- exists path
        | False => pure (MkRun changed stays saved made)
      Right s <- Subject.load path
        | Left e =>
          pure (MkRun changed (("the file", "it does not parse: " ++ e) :: stays) saved made)
      others <- if r.wide then project else pure (MkProject [] [] Nothing [])
      let left = filter (\c => not (c.label `elem` map fst stays)) (r.candidates others s)
      case left of
        [] => pure (MkRun changed stays saved made)
        (c :: _) =>
          if c.label `elem` changed
            then loop checked check changed ((c.label, "it comes back after its change") :: stays)
              saved made else
          case c.plan of
            Left why => loop checked check changed ((c.label, why) :: stays) saved made
            Right ch => do
              result <- attempt (if checked then c.preferred else Nothing) ch
              case result of
                Left why => loop checked check changed ((c.label, why) :: stays) saved made
                Right (before, ch') => do
                  changedFiles
                  -- what a file was before the run is kept, not what it
                  -- was before this change
                  loop checked check (c.label :: changed) stays (mergeLeft saved before)
                    ((c.label, before, ch') :: made)
      where
        -- the preferred change if there is one and it checks, else the
        -- change; what the files were before it, and the change made
        attempt : Maybe Change -> Change -> IO (Either String (Saved, Change))
        attempt (Just p) ch = do
          tried <- makeChange check p
          case tried of
            Right before => pure (Right (before, p))
            Left _ => map (\b => (b, ch)) <$> makeChange check ch
        attempt Nothing ch = map (\b => (b, ch)) <$> makeChange check ch

    ||| The run made unchecked, then every file it touched checked once, with
    ||| all its changes; made again, a check after each change, if one fails.
    checkedOnce : (cmd : String) -> IO Report
    checkedOnce cmd = do
      unchecked <- loop True Nothing [] [] empty []
      -- the Idris files the run touched that are there after it
      there <- traverse (\p => (p,) <$> exists p)
        (filter (isSuffixOf ".idr") (keys unchecked.saved))
      let touched = map fst (filter snd there)
      Nothing <- failsOn cmd touched
        | Just _ => do
            restore unchecked.saved
            changedFiles
            loop True (Just cmd) [] [] empty [] >>= finish
      finish unchecked

||| The refactoring run over the file at the path to a fixed point: each
||| ready candidate changed, or recorded as staying, until none is left. A
||| candidate that comes back after its change stays, so the run ends. The
||| `check`, if any, is a shell command with `{}` where a file's path goes,
||| which succeeds on a file that checks. A wide refactoring's `project`
||| may be kept between calls; `changed` says the files no longer are what
||| it was read from. A dry run prints its changes at the end, those of the
||| run that stood.
export
refactor : (dryRun : Bool) -> (check : Maybe String) -> Refactoring -> (project : IO Project) ->
           (changed : IO ()) -> (path : String) -> IO Report
refactor dryRun check r project changedFiles path = do
  aside <- newIORef []
  runWith aside dryRun check r project changedFiles path
