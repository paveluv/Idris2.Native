||| `idris2-native-lint`: the rules of the product's code, checked on Idris's
||| own parse of each file.
|||
|||   idris2-native-lint [--golden | --fix | --warnings] [--health [--minimum N] [--offenders N]] [--resolved] PATH... [--programs PATH...]
|||
||| Each path is a `.idr` file or a directory, walked for `.idr` files, its
||| `build` directories left out. The paths after `--programs` are programs
||| (tests, examples), bound by the rules about what a file says of itself
||| and the order of its imports, not by those of the product's code.
||| The findings print with their positions, or with `--golden` without them,
||| sorted, the form the gate compares; `--health` prints the architectural
||| health score of the files instead, and with `--minimum` fails below it;
||| `--offenders N` lists under each component short of 100 the `N` that
||| cost it most: what each is about, its cost in the units the component
||| counts, and what the cost is made of.
||| `--fix` puts each file's imports in order first, the one rule the linter
||| fixes by itself. A rule's findings are errors or, for advice, warnings:
||| `--warnings` prints those too, and they fail nothing. The exit status is
||| 1 when there are errors or the score is too low.
|||
||| `--resolved` adds the rules over what the modules use, resolved from the
||| TTCs their build wrote (`Lint.Resolution`), and the components of the
||| score they measure: the modules must be built first, and a module whose
||| TTC is missing or older than its source is a finding, the rules over the
||| resolution then not run. The programs are not resolved.
|||
||| A finding is suppressed by a comment, `-- lint: allow <rule>: <reason>`,
||| on its line or in the lines above it up to a blank line: a suppression
||| covers its paragraph from where it stands. A suppression without a
||| reason, of no rule, or that suppresses nothing, is a finding itself.
module Lint.Main

import Data.Either
import Data.List
import Data.SortedSet
import Data.String
import Idris.Syntax
import Lint.Finding
import Lint.Fix
import Lint.Graph
import Lint.Resolution
import Lint.ResolvedRules
import Lint.Rules
import Lint.Source
import System
import System.Directory

%default covering

------------------------------------------------------------------------------
-- Files

||| The `.idr` files under a path, in order.
files : String -> IO (List String)
files path =
  if isSuffixOf ".idr" path then pure [path] else do
    Right entries <- listDir path
      | Left _ => pure []
    let children = sort [ path ++ "/" ++ e | e <- entries, e /= ".", e /= "..", e /= "build" ]
    joined <$> traverse files children

------------------------------------------------------------------------------
-- Suppressions

||| A suppression: its rule, its reason, where its comment is, and the
||| last line it covers.
record Suppression where
  constructor MkSuppression
  rule : String
  reason : String
  line : Int
  col : Int
  through : Int

suppressions : SourceFile -> List Suppression
suppressions f = mapMaybe one f.comments
  where
    one : SourceComment -> Maybe Suppression
    one c =
      if c.isDoc || not (isPrefixOf "lint: allow " c.text) then Nothing else
        let rest = substr 12 (length c.text) c.text
            (r, why) = break (== ':') rest
            -- to the line before the next blank one
            through = maybe 2147483647 (\b => b - 1) (find (> c.line) f.blankLines)
        in Just (MkSuppression (trim r) (trim (substr 1 (length why) why)) c.line c.col through)

covers : Suppression -> Finding -> Bool
covers s fi = fi.rule == s.rule && fi.line >= s.line && fi.line <= s.through

||| The findings a file's suppressions leave, and the findings about the
||| suppressions themselves.
suppress : SourceFile -> List Finding -> List Finding
suppress f fs =
  let ss = suppressions f
      kept = filter (\fi => fi.path /= f.path || not (any (\s => covers s fi) ss)) fs
  in kept ++ joined (map (check fs) ss)
  where
    check : List Finding -> Suppression -> List Finding
    check fs s =
      let at = MkFinding "suppression" f.path s.line s.col s.rule in
      if not (s.rule `elem` ruleNames) then [at ("no rule `" ++ s.rule ++ "`")]
      else if s.reason == "" then [at ("a suppression of `" ++ s.rule ++ "` says why")]
      else if not (any (\fi => fi.path == f.path && covers s fi) fs) then [at ("the suppression of `" ++ s.rule ++ "` suppresses nothing")]
      else []

------------------------------------------------------------------------------
-- Running

||| What the linter is asked to do.
record Request where
  constructor MkRequest
  golden : Bool
  fix : Bool
  warnings : Bool
  health : Bool
  minimum : Maybe Nat
  offenders : Nat
  resolved : Bool
  paths : List String
  programs : List String
  inPrograms : Bool

request : List String -> Request
request = go (MkRequest False False False False Nothing 0 False [] [] False)
  where
    go : Request -> List String -> Request
    go o [] = o
    go o ("--golden" :: as) = go ({ golden := True } o) as
    go o ("--fix" :: as) = go ({ fix := True } o) as
    go o ("--warnings" :: as) = go ({ warnings := True } o) as
    go o ("--health" :: as) = go ({ health := True } o) as
    go o ("--minimum" :: n :: as) = go ({ minimum := Just (cast n) } o) as
    go o ("--resolved" :: as) = go ({ resolved := True } o) as
    go o ("--offenders" :: k :: as) = go ({ offenders := cast k } o) as
    go o ("--programs" :: as) = go ({ inPrograms := True } o) as
    go o (p :: as) = go (if o.inPrograms then { programs $= (++ [p]) } o else { paths $= (++ [p]) } o) as

||| The findings of the product's files and of the programs, suppressions
||| applied: those of the resolved rules too, given the resolution, or the
||| findings that kept it from being made.
lint : List (SourceFile, List Declared, Mentions) -> List SourceFile -> Maybe (Either (List Finding) Resolution) -> List Finding
lint fdms ps res =
  let fs = map (\(f, _, _) => f) fdms
      fds = map (\(f, ds, _) => (f, ds)) fdms
      resolved = case res of
        Nothing => []
        Just (Left problems) => problems
        Just (Right r) => resolvedRules fdms r
      ours = the (SortedSet String) (fromList (map (\f => show f.mod.moduleNS) fs))
      aliases = joined (map (\(f, _, ms) => importAlias ours f ms.refs) fdms)
      all = joined (map (\(f, ds, ms) => fileRules f ms ds) fdms) ++ joined (map programRules ps) ++ graphRules fs ++ sameName fds
            ++ parentUnique fs ++ aliases ++ resolved
  in sort (foldl (\acc, f => suppress f acc) all (fs ++ ps))

||| The files under the paths, parsed, and a finding for each that does not
||| parse.
parsed : List String -> IO (List SourceFile, List Finding)
parsed roots = do
  paths <- joined <$> traverse files roots
  results <- traverse parse paths
  let failures = mapMaybe (\(p, r) => either (\e => Just (MkFinding "parse" p 0 0 "" e)) (const Nothing) r) (zip paths results)
  pure (rights results, failures)

||| The files under a path with their imports put in order, where they were
||| not.
fixImports : String -> IO ()
fixImports root = do
  paths <- files root
  for_ paths $ \p => do
    Right f <- parse p
      | Left _ => pure ()
    Right text <- readFile p
      | Left _ => pure ()
    let ls = lines text
        fixed = orderImports f ls
    when (fixed /= ls) $ do
      Right () <- writeFile p (unlines fixed)
        | Left err => putStrLn (p ++ ": " ++ show err)
      putStrLn ("imports put in order: " ++ p)

||| A component's offenders that cost it most, the first `n`, the costliest
||| first, and among equal costs in the order of their subjects.
worst : Nat -> List Offender -> List Offender
worst n os = take n (sortBy (\a, b => compare (negate (cast {to = Integer} a.cost), a.subject) (negate (cast b.cost), b.subject)) os)

offender : Offender -> IO ()
offender x = putStrLn ("      " ++ padLeft 5 ' ' (show x.cost) ++ "  " ++ x.subject ++ ": " ++ x.detail)

||| The components of a group.
inGroup : String -> List Component -> List Component
inGroup g = filter (\c => c.group == g)

||| A component's line, and under it, short of 100, its worst `n` offenders.
component : (n : Nat) -> Component -> IO ()
component n c = do
  putStrLn ("    " ++ padRight 14 ' ' c.name ++ padLeft 3 ' ' (show c.value) ++ "  " ++ c.counted)
  when (c.value /= 100) $ traverse_ offender (worst n c.offenders)

main : IO ()
main = do
  (_ :: args) <- getArgs
    | [] => exitWith (ExitFailure 2)
  let o = request args
  when (null o.paths && null o.programs) $ do
    putStrLn "usage: idris2-native-lint [--golden | --fix | --warnings] [--health [--minimum N] [--offenders N]] [--resolved] PATH... [--programs PATH...]"
    exitWith (ExitFailure 2)
  when o.fix $ traverse_ fixImports (o.paths ++ o.programs)
  (fs, failed) <- parsed o.paths
  (ps, failedPrograms) <- parsed o.programs
  fdms <- traverse (\f => do ds <- declared f; ms <- mentions f.mod.decls; pure (f, ds, ms)) fs
  let fds = map (\(f, ds, _) => (f, ds)) fdms
  res <- if o.resolved then Just <$> resolve fs else pure Nothing
  if o.health
    then do
      r <- case res of
        Just (Left problems) => do
          traverse_ (putStrLn . withPosition) problems
          exitWith (ExitFailure 2)
        Just (Right r) => pure (Just r)
        Nothing => pure Nothing
      let cs = health fds ++ maybe [] (resolvedHealth fdms) r
          overall = score cs
      putStrLn ("architectural health: " ++ show overall)
      for_ (groups cs) $ \g => do
        putStrLn ("  " ++ padRight 16 ' ' g ++ padLeft 3 ' ' (show (groupScore cs g)))
        traverse_ (component o.offenders) (inGroup g cs)
      whenJust o.minimum $ \m => when (overall < m) $ do
        putStrLn ("below the minimum, " ++ show m)
        exitWith (ExitFailure 1)
    else do
      let findings = (failed ++ failedPrograms) ++ lint fdms ps res
      let errors = filter (not . isWarning . (.rule)) findings
          shown = if o.warnings && not o.golden then findings else errors
      traverse_ (putStrLn . if o.golden then withoutPosition else withPosition) shown
      when (not (null errors) && not o.golden) $ exitWith (ExitFailure 1)
