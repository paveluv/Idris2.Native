||| `idris2-native-lint`: the rules of the product's code, checked on Idris's
||| own parse of each file.
|||
||| idris2-native-lint [--golden | --fix] [--health [--minimum N] [--offenders
||| N]]
|||     [--helpers] [--refactor NAME [--arg VALUE]... [--dry-run] [--check COMMAND]]
|||     [--resolved] PATH... [--unscored PATH...] [--programs PATH...]
|||
||| Each path is a `.idr` file or a directory, walked for `.idr` files, its
||| `build` directories left out. The paths after `--unscored` are bound by
||| the rules of the product's code but left out of the score (the linter's
||| own). The paths after `--programs` are programs (tests, examples), bound
||| by the rules about what a file says of itself and the order of its
||| imports, not by those of the product's code.
||| The findings print with their positions, or with `--golden` without them,
||| sorted, the form the gate compares; `--minimum N` prints after them the
||| architectural health score of the files before `--unscored`, and fails
||| below `N`: the gate's run, which parses and resolves the files once for
||| both; `--health` prints the score instead of the findings;
||| `--offenders N` lists under each component short of 100 the `N` that
||| cost it most: what each is about, its cost in the units the component
||| counts, and what the cost is made of.
||| `--helpers` lists instead the private functions each used by one other
||| declaration and left module-wide, with their positions and that one:
||| what the scoping component counts against, each to move into its user's
||| `where` block.
||| `--refactor NAME` changes the code instead, by the refactoring of that
||| name (`refactorings`), each file to a fixed point, and reports each
||| file's changes and what stays, with why; with `--dry-run` it prints the
||| changes and puts every file back; with `--check` it undoes a change
||| after which the command fails on a file the change touched, the file's
||| path in the place of `{}` (`make check-source SOURCE={}`). A
||| refactoring may take arguments, each by `--arg` (`split-module`: the
||| module to make, then the concepts to move into it; `join-modules`: the
||| module to make, then the modules to join; `rename-module`: the module,
||| then its new name; `inline-alias`: the function; `reflow-lines`: the
||| width), and one whose
||| changes only the type checker can judge runs only with `--check`
||| (`prune-imports`). `--fix`
||| puts each file's imports in order first: the refactoring
||| `order-imports`, the one rule the linter fixes by itself. The exit status
||| is 1 when there are findings or the score is too low.
|||
||| `--resolved` adds the rules over what the modules use, resolved from the
||| TTCs their build wrote (`Lint.Resolution`), and the components of the
||| score they measure: the modules must be built first, and a module whose
||| TTC is missing or older than its source is a finding, the rules over the
||| resolution then not run. The programs are not resolved.
|||
||| A finding is suppressed by a comment, `-- lint: allow <rule>: <reason>`,
||| on its line or in the lines above it up to a blank line: a suppression
||| covers its paragraph from where it stands. Of a rule that asks why at
||| each use (`ResolvedRules.oneUseRules`), it covers only the first finding
||| from where it stands, so that each use has a reason of its own; of a
||| rule no suppression lifts (`Rules.unsuppressibleRules`), it is a
||| finding itself, and so is one of an unused or public import for the flat
||| check, which loads every module a flat function reaches. A suppression
||| without a
||| reason, of no rule, or that suppresses nothing, is a finding itself. A
||| module is left out of a component of the score by another comment,
||| `-- lint: exclude <component>: <reason>` (`Exclusion`).
module Lint.Main

import Lint.Distinction
import Lint.Finding
import Lint.Graph
import Lint.Refactor.InlineAlias
import Lint.Refactor.JoinModules
import Lint.Refactor.MergeClauses
import Lint.Refactor.OrderImports
import Lint.Refactor.Project
import Lint.Refactor.PruneImports
import Lint.Refactor.QualifyNames
import Lint.Refactor.Refactoring
import Lint.Refactor.ReflowLines
import Lint.Refactor.RemoveUnused
import Lint.Refactor.Rename
import Lint.Refactor.RenameModule
import Lint.Refactor.ScopeHelpers
import Lint.Refactor.SplitModule
import Lint.Refactor.Subject
import Lint.Refactor.Unprime
import Lint.Resolution
import Lint.ResolvedRules
import Lint.Rules
import Lint.Source

import Core.FC
import Core.Name
import Core.Name.Namespace
import Core.WithData
import Data.Either
import Data.IORef
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Data.String
import Data.Zippable
import Idris.Syntax
import System
import System.Directory
import System.File.Error

%default covering

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

------------------------------------------------------------------------------
-- Running

||| Which of a run's paths a path given is: one of the files scored, one
||| bound by the rules and not scored, or a program's.
data Section = Scored | Unscored | Programs

||| What the linter is asked to do.
record Request where
  constructor MkRequest
  golden : Bool
  fix : Bool
  health : Bool
  minimum : Maybe Nat
  offenders : Nat
  resolved : Bool
  listHelpers : Bool
  refactoring : Maybe String
  dryRun : Bool
  checkCommand : Maybe String
  arguments : List String
  paths : List String
  unscored : List String
  programs : List String
  section : Section

main : IO ()
main = do
  (_ :: args) <- getArgs
    | [] => exitWith (ExitFailure 2)
  let o = request args
  when (null o.paths && null o.unscored && null o.programs) $ do
    putStrLn
      ("usage: idris2-native-lint [--golden | --fix] [--health [--minimum N] [--offenders N]] " ++
       "[--helpers] [--refactor NAME [--arg VALUE]... [--dry-run] [--check COMMAND]] " ++
       "[--resolved] PATH... [--unscored PATH...] [--programs PATH...]")
    exitWith (ExitFailure 2)
  when o.fix $ runRefactoring True False Nothing orderImports (o.paths ++ o.unscored ++ o.programs)
  whenJust o.refactoring $ \n => do
    case find (\r => r.name == n) (refactorings o.arguments) of
      Nothing => do
        putStrLn
          ("no refactoring `" ++ n ++ "`; there are "
           ++ fastConcat (intersperse ", " (map (.name) (refactorings []))))
        exitWith (ExitFailure 2)
      Just r => do
        when (r.needsCheck && isNothing o.checkCommand) $ do
          putStrLn
            ("`" ++ n ++ "` runs only with `--check`: only the type checker can judge its changes")
          exitWith (ExitFailure 2)
        runRefactoring False o.dryRun o.checkCommand r (o.paths ++ o.unscored ++ o.programs)
        exitWith ExitSuccess
  (fs, failed) <- parsed o.paths
  (us, failedUnscored) <- parsed o.unscored
  (ps, failedPrograms) <- parsed o.programs
  scored <- traverse declaredIn fs
  fdms <- (scored ++) <$> traverse declaredIn us
  let fds = map (\(f, ds, _) => (f, ds)) fdms
  when o.listHelpers $ do
    traverse_ (\(f, ds) => traverse_ (putStrLn . singleUse f) (fst (helpers ds))) fds
    exitWith ExitSuccess
  res <- if o.resolved then Just <$> resolve (fs ++ us) else pure Nothing
  findings <- the (IO (List Finding)) $ if o.health then pure [] else do
    pms <- traverse (\f => mentions f.mod.decls) ps
    let programNames =
          the (SortedSet String) (fromList (joined (map (\m => map (nameRoot . snd) m.refs) pms)))
        findings = (failed ++ failedUnscored ++ failedPrograms) ++ lint fdms ps programNames res
    traverse_ (putStrLn . if o.golden then withoutPosition else withPosition) findings
    pure findings
  low <- if not o.health && isNothing o.minimum then pure False else case res of
    -- the findings print them, when they are asked for
    Just (Left problems) => do
      when o.health $ do
        traverse_ (putStrLn . withPosition) problems
        exitWith (ExitFailure 2)
      pure False
    Just (Right r) =>
      healthOf o scored (Just ({ modules $= filter (\rm => rm.path `elem` map (.path) fs) } r))
    Nothing => healthOf o scored Nothing
  when (not o.golden && (not (null findings) || low)) $ exitWith (ExitFailure 1)
  where
    request : List String -> Request
    request =
      go
        (MkRequest False False False Nothing 0 False False Nothing False Nothing [] [] [] [] Scored)
      where
        go : Request -> List String -> Request
        go o [] = o
        go o ("--golden" :: as) = go ({ golden := True } o) as
        go o ("--fix" :: as) = go ({ fix := True } o) as
        go o ("--health" :: as) = go ({ health := True } o) as
        go o ("--minimum" :: n :: as) = go ({ minimum := Just (cast n) } o) as
        go o ("--resolved" :: as) = go ({ resolved := True } o) as
        go o ("--helpers" :: as) = go ({ listHelpers := True } o) as
        go o ("--refactor" :: n :: as) = go ({ refactoring := Just n } o) as
        go o ("--dry-run" :: as) = go ({ dryRun := True } o) as
        go o ("--check" :: c :: as) = go ({ checkCommand := Just c } o) as
        go o ("--arg" :: a :: as) = go ({ arguments $= (++ [a]) } o) as
        go o ("--offenders" :: k :: as) = go ({ offenders := cast k } o) as
        go o ("--unscored" :: as) = go ({ section := Unscored } o) as
        go o ("--programs" :: as) = go ({ section := Programs } o) as
        go o (p :: as) = go (case o.section of
                               Scored => { paths $= (++ [p]) } o
                               Unscored => { unscored $= (++ [p]) } o
                               Programs => { programs $= (++ [p]) } o) as

    ||| The findings of the product's files and of the programs, suppressions
    ||| applied: those of the resolved rules too, given the resolution, or the
    ||| findings that kept it from being made. A suppression of a resolved
    ||| rule suppresses nothing without the resolution, and is not reported
    ||| for it then.
    lint : List (SourceFile, List Declared, Mentions) -> List SourceFile ->
           (programNames : SortedSet String) ->
           Maybe (Either (List Finding) Resolution) -> List Finding
    lint fdms ps programNames res =
      let fs = map (\(f, _, _) => f) fdms
          fds = map (\(f, ds, _) => (f, ds)) fdms
          ran = case res of
            Just (Right _) => True
            _ => False
          resolved = case res of
            Nothing => []
            Just (Left problems) => problems
            Just (Right r) => resolvedRules fdms programNames r
          ours = the (SortedSet String) (fromList (map (\f => show f.mod.moduleNS) fs))
          exportsOf =
            the (SortedMap String (List String))
              (fromList [ (show f.mod.moduleNS, joined (map (.visible) ds)) | (f, ds) <- fds ])
          aliases =
            joined
              (map
                (\(f, ds, ms) => importAlias exportsOf f ms.refs
                 ++ selfQualified f (joined (map (.defines) ds)) ms.refs)
               fdms)
          all = joined (map (\(f, ds, ms) => fileRules f ms ds) fdms)
            ++ joined (map programRules ps) ++ graphRules fs
                ++ aliases ++ joined (map exclusionRules fs) ++ resolved
      in sort (foldl (\acc, f => suppress ran f acc) all (fs ++ ps))
      where
        ||| The findings a file's suppressions leave, and the findings about the
        ||| suppressions themselves.
        suppress : (ran : Bool) -> SourceFile -> List Finding -> List Finding
        suppress ran f fs =
          let ss = suppressions f
              kept = filter (\fi => fi.path /= f.path || not (any (\s => covers s fi) ss)) fs
          in kept ++ joined (map (check fs) ss)
          where
            -- whether a reason is the flat check's, or the flat translation's
            forTheFlatCheck : String -> Bool
            forTheFlatCheck r = isInfixOf "flat check" r || isInfixOf "flat translation" r

            covers : Suppression -> Finding -> Bool
            covers s fi =
              fi.rule == s.rule && fi.line >= s.line && fi.line <= s.through
              && not (s.rule `elem` unsuppressibleRules)
              && (not (s.rule `elem` oneUseRules) || Just (fi.line, fi.col) == firstFrom s)
              where
                -- the first finding of the rule in the suppression's paragraph
                firstFrom : Suppression -> Maybe (Int, Int)
                firstFrom s =
                  head' (sort [ (g.line, g.col) | g <- fs, g.path == f.path, g.rule == s.rule
                                                            , g.line >= s.line,
                                                              g.line <= s.through ])

            check : List Finding -> Suppression -> List Finding
            check fs s =
              let at = MkFinding "suppression" f.path s.line s.col s.rule in
              if not (s.rule `elem` ruleNames ++ resolvedRuleNames)
                then [at ("no rule `" ++ s.rule ++ "`")]
              else if s.rule `elem` unsuppressibleRules
                then [at ("`" ++ s.rule ++ "` is not to be suppressed: change what it reports")]
              else if (s.rule == "import-unused" || s.rule == "public-import")
                && forTheFlatCheck s.reason
                then
                  [at
                    (("the flat check loads every module a flat function reaches: no import is " ++
                      "kept, nor re-exported, for it"))]
              else if s.reason == "" then [at ("a suppression of `" ++ s.rule ++ "` says why")]
              else if not ran && (s.rule `elem` resolvedRuleNames) then []
              else if not (any (\fi => fi.path == f.path && covers s fi) fs)
                then [at ("the suppression of `" ++ s.rule ++ "` suppresses nothing")]
              else []

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
                    in Just
                      (MkSuppression (trim r) (trim (substr 1 (length why) why)) c.line c.col
                       through)

    ||| The `.idr` files under a path, in order.
    files : String -> IO (List String)
    files path =
      if isSuffixOf ".idr" path then pure [path] else do
        Right entries <- listDir path
          | Left _ => pure []
        let children = sort [ path ++ "/" ++ e | e <- entries, e /= ".", e /= "..", e /= "build" ]
        joined <$> traverse files children

    ||| The files under the paths, parsed, and a finding for each that does not
    ||| parse.
    parsed : List String -> IO (List SourceFile, List Finding)
    parsed roots = do
      paths <- joined <$> traverse files roots
      results <- traverse parse paths
      let failures =
            mapMaybe
              (\(p, r) => either (\e => Just (MkFinding "parse" p 0 0 "" e)) (const Nothing) r)
                (zip paths results)
      pure (rights results, failures)

    ||| The refactorings, by name, given the run's arguments (`--arg`), which
    ||| those that take them read: `split-module` the module to make and the
    ||| concepts to move to it.
    refactorings : List String -> List Refactoring
    refactorings args =
      [inlineAlias args, joinModules args, mergeClauses, orderImports, pruneImports, qualifyNames,
        reflowLines args, removeUnused, rename args, renameModule args, scopeHelpers,
       splitModule args, unprime]

    ||| The files under a run's roots listed and parsed once, and again only
    ||| after a change, which may have moved one: a wide refactoring asks
    ||| for them at every file it looks at.
    projectOnce : IORef (Maybe Project) -> (roots : List String) -> Maybe Resolution ->
                  List Subject -> IO Project
    projectOnce cache roots res context = do
      Nothing <- readIORef cache
        | Just p => pure p
      -- the files as they are now: a change may have moved one
      paths <- joined <$> traverse files roots
      p <- loadProject roots paths res context
      writeIORef cache (Just p)
      pure p

    ||| The modules of the packages beside the roots, but the run's own files,
    ||| parsed.
    contextOf : (roots, paths : List String) -> IO (List Subject)
    contextOf roots paths = do
      packages <- packagesNear roots
      others <- joined <$> traverse (\(pp, t) => files (sourceDirOf pp t)) packages
      rights <$> traverse load (filter (\o => not (o `elem` paths)) (nub others))

    ||| What the files' modules use, resolved, those whose TTCs can be read.
    resolvedFrom : List String -> IO (Maybe Resolution)
    resolvedFrom paths = do
      fs <- rights <$> traverse parse paths
      res <- resolve fs
      case res of
        Right r => pure (Just r)
        -- the files whose TTCs are missing or stale, such as programs that
        -- are not built, left out: the rest resolved
        Left problems =>
          let missing = map (.path) problems
              rest = filter (\f => not (f.path `elem` missing)) fs
          in if null missing || length rest == length fs then pure Nothing
             else either (const Nothing) Just <$> resolve rest

    ||| The refactoring run over every file under the paths, each to a fixed
    ||| point, with what it changed and what stays printed unless `quiet`.
    runRefactoring : (quiet, dryRun : Bool) -> (check : Maybe String) -> Refactoring ->
                     List String -> IO ()
    runRefactoring quiet dryRun check r roots = do
      paths <- joined <$> traverse files roots
      cache <- newIORef Nothing
      -- what the modules use, read once from the TTCs built before the run,
      -- which its changes leave behind
      res <- if r.wide then resolvedFrom paths else pure Nothing
      -- the modules of the packages beside the roots that the run's files
      -- may import, read once, as the run does not change them
      context <- if r.wide then contextOf roots paths else pure []
      for_ paths $ \p => do
        rep <- refactor dryRun check r (projectOnce cache roots res context)
          (writeIORef cache Nothing) p
        when (not quiet || not (null rep.changed)) $
          when (not (null rep.changed) || not (null rep.stays)) $ do
            putStrLn
              (p ++ ": " ++ show (length rep.changed) ++ " changed, " ++ show (length rep.stays)
               ++ " stay")
            for_ rep.stays $ \(what, why) => putStrLn ("  `" ++ what ++ "` stays: " ++ why)

    ||| The components of a group.
    inGroup : String -> List Component -> List Component
    inGroup g = filter (\c => c.group == g)

    ||| A component's line, and under it, short of 100, its worst `n` offenders.
    component : (n : Nat) -> Component -> IO ()
    component n c = do
      putStrLn
        ("    " ++ padRight 14 ' ' c.name ++ padLeft 3 ' ' (show c.value) ++ "  " ++ c.counted)
      when (c.value /= 100) $ traverse_ offender (worst n c.offenders)
      where
        ||| A component's offenders that cost it most, the first `n`, the costliest
        ||| first, and among equal costs in the order of their subjects.
        worst : Nat -> List Offender -> List Offender
        worst n os =
          take n
            (sortBy (\a,
              b =>
                compare (negate (cast {to = Integer} a.cost), a.subject)
                     (negate (cast b.cost), b.subject))
             os)

        offender : Offender -> IO ()
        offender x =
          putStrLn
            ("      " ++ padLeft 5 ' ' (show x.cost) ++ "  " ++ x.subject ++ ": " ++ x.detail)

    ||| A helper used by one declaration, as `--helpers` prints it: where it is
    ||| declared, its name, and its user with where that starts.
    singleUse : SourceFile -> (Declared, Declared) -> String
    singleUse f (h, u) =
      f.path ++ ":" ++ show (line h) ++ " `" ++ name h ++ "` used only by `" ++ name u ++ "` at "
        ++ show (line u)
      where
        line : Declared -> Int
        line d = case d.decl.fc of
          MkFC _ (l, _) _ => l + 1
          MkVirtualFC _ (l, _) _ => l + 1
          EmptyFC => 0

        name : Declared -> String
        name d = fromMaybe "?" (head' d.defines)

    ||| A file with its declarations and what it mentions.
    declaredIn : SourceFile -> IO (SourceFile, List Declared, Mentions)
    declaredIn f = do
      ds <- declared f
      ms <- mentions f.mod.decls
      pure (f, ds, ms)

    ||| The health score of the files, with its groups and their components,
    ||| printed; whether it is below the minimum asked for.
    healthOf : Request -> List (SourceFile, List Declared, Mentions) -> Maybe Resolution -> IO Bool
    healthOf o fdms r = do
      let fds = map (\(f, ds, _) => (f, ds)) fdms
          cs = health fds ++ [distinction fds] ++ maybe [] (resolvedHealth fdms) r
          overall = score cs
      putStrLn ("architectural health: " ++ show overall)
      for_ (groups cs) $ \g => do
        putStrLn ("  " ++ padRight 16 ' ' g ++ padLeft 3 ' ' (show (groupScore cs g)))
        traverse_ (component o.offenders) (inGroup g cs)
      case o.minimum of
        Just m => if overall < m
                    then do putStrLn ("below the minimum, " ++ show m)
                            pure True
                    else pure False
        Nothing => pure False
