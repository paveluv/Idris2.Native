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
||| same, printing each change, and puts every file back at the end. Only
||| the Idris files a change touches are parsed and checked again.
|||
||| Parsing is all the linter itself can ask of a change. A run may be given
||| a check besides, a command that type checks a file, and a change any
||| touched file fails it after is undone too: the type checker is the
||| judge of what a planner could only reason about.
module Lint.Refactor.Refactoring

import Lint.Refactor.Change
import Lint.Refactor.Edit
import Lint.Refactor.Project
import Lint.Refactor.Span
import Lint.Refactor.Subject

import Core.WithData
import Data.List
import Data.List1
import Data.Maybe
import Data.SortedMap
import Data.String
import Idris.Syntax
import Libraries.Data.WithData
import Lint.Rules
import Lint.Source
import System
import System.Directory
import System.File.Error
import System.File.Meta
import System.File.ReadWrite

%default covering

||| One thing a refactoring may change: what it is about, for the report,
||| and its change, or why it stays as it is.
public export
record Candidate where
  constructor MkCandidate
  label : String
  plan : Either String Change

||| What a declaration is called in a report: the names it defines, or,
||| for one that defines none, such as an implementation, where it is.
export
labelOf : Declared -> String
labelOf d = case d.defines of
  [] => "the declaration at line " ++ show (fst (lineSpan d.decl.fc) + 1)
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

||| The refactoring run over the file at the path to a fixed point: each
||| ready candidate changed, or recorded as staying, until none is left. A
||| candidate that comes back after its change stays, so the run ends. The
||| `check`, if any, is a shell command with `{}` where a file's path goes,
||| which succeeds on a file that checks. A wide refactoring's `project`
||| may be kept between calls; `changed` says the files no longer are what
||| it was read from.
export
refactor : (dryRun : Bool) -> (check : Maybe String) -> Refactoring -> (project : IO Project) -> (changed : IO ()) -> (path : String) -> IO Report
refactor dryRun check r project changedFiles path = loop [] [] empty
  where
    ||| The files a change touches, as they were before it: `Nothing` for a file
    ||| it creates.
    Saved : Type
    Saved = SortedMap String (Maybe String)

    restore : Saved -> IO ()
    restore saved = for_ (SortedMap.toList saved) $ \(p, old) => case old of
      Just t => ignore (writeFile p t)
      Nothing => ignore (removeFile p)

    finish : List String -> List (String, String) -> Saved -> IO Report
    finish changed stays saved = do
      when dryRun $ restore saved
      pure (MkReport path (reverse changed) (reverse stays))

    ||| A change made: each file edited and each created, what each was kept,
    ||| and every touched file parsed, and checked, again; or, with everything
    ||| put back, why it could not be made.
    makeChange : Change -> IO (Either String Saved)
    makeChange ch = do
      Right saved <- editAll empty ch.edits
        | Left (why, saved) => do restore saved; pure (Left why)
      Right saved' <- createAll saved ch.created
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
        sources saved = filter (isSuffixOf ".idr") (keys saved)

        editAll : Saved -> List (String, List Edit) -> IO (Either (String, Saved) Saved)
        editAll saved [] = pure (Right saved)
        editAll saved ((p, es) :: rest) = do
          Right old <- readFile p
            | Left e => pure (Left ("cannot read " ++ p ++ ": " ++ show e, saved))
          let saved' = if isJust (lookup p saved) then saved else insert p (Just old) saved
          case apply es old of
            Nothing => pure (Left ("its edits to " ++ p ++ " overlap", saved'))
            Just new => do
              Right () <- writeFile p new
                | Left e => pure (Left ("cannot write " ++ p ++ ": " ++ show e, saved'))
              editAll saved' rest

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
          r <- parse p
          case r of
            Left e => pure (Just ("the change leaves " ++ p ++ " unparsed: " ++ e))
            Right _ => unparsed ps

        -- the first touched file the check fails on, if there is a check
        unchecked : List String -> IO (Maybe String)
        unchecked ps = case check of
          Nothing => pure Nothing
          Just cmd => go cmd ps
          where
            withPath : String -> String -> String
            withPath p cmd = case break (== '{') (unpack cmd) of
              (before, '{' :: '}' :: after) => pack before ++ p ++ withPath p (pack after)
              (before, c :: after) => pack (before ++ [c]) ++ withPath p (pack after)
              (before, []) => pack before

            go : String -> List String -> IO (Maybe String)
            go _ [] = pure Nothing
            go cmd (p :: more) = do
              0 <- system (withPath p cmd)
                | _ => pure (Just ("the change leaves " ++ p ++ " not checking"))
              go cmd more

    ||| A change as a dry run prints it: each edit, with the text it replaces.
    printChange : Saved -> Change -> IO ()
    printChange saved ch = do
      for_ ch.edits $ \(p, es) => do
        putStrLn ("  " ++ p)
        let old = fromMaybe "" (join (lookup p saved))
        for_ es $ \e => traverse_ (putStrLn . ("    " ++)) (describe old e)
      for_ ch.created $ \(p, _) => putStrLn ("  created " ++ p)

    loop : List String -> List (String, String) -> Saved -> IO Report
    loop changed stays saved = do
      Right s <- load path
        | Left e => finish changed (("the file", "it does not parse: " ++ e) :: stays) saved
      others <- if r.wide then project else pure (MkProject [] [])
      let left = filter (\c => not (c.label `elem` map fst stays)) (r.candidates others s)
      case left of
        [] => finish changed stays saved
        (c :: _) =>
          if c.label `elem` changed then loop changed ((c.label, "it comes back after its change") :: stays) saved else
          case c.plan of
            Left why => loop changed ((c.label, why) :: stays) saved
            Right ch => do
              made <- makeChange ch
              case made of
                Left why => loop changed ((c.label, why) :: stays) saved
                Right before => do
                  changedFiles
                  when dryRun $ do
                    putStrLn (r.name ++ ": " ++ c.label)
                    printChange before ch
                  -- what a file was before the run is kept, not what it
                  -- was before this change
                  loop (c.label :: changed) stays (mergeLeft saved before)
