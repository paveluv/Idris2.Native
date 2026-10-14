||| The import graph of the modules linted together: the rules over it, and
||| the architectural health score.
|||
||| A module's layer is told by its name. Of our modules, a layer imports only
||| those of the layers below it; a module of no layer (a program, a test) may
||| import any. The runtime imports nothing from the libraries but what it
||| shares with the compiler.
module Lint.Graph

import Core.FC
import Core.Name
import Core.Name.Namespace
import Core.WithData
import Data.List
import Data.List1
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Data.String
import Idris.Syntax
import Libraries.Data.WithData
import Lint.Finding
import Lint.Rules
import Lint.Source

%default covering

------------------------------------------------------------------------------
-- Layers

||| The layers of the product, from the bottom: `Data` (structures any part
||| may use), `Flat` (the flat fragment, of no backend), `Native` (the code
||| generator), `Runtime` (the runtime library), and the linter's own.
data Layer = DataLayer | FlatLayer | NativeLayer | RuntimeLayer | LintLayer

Eq Layer where
  DataLayer == DataLayer = True
  FlatLayer == FlatLayer = True
  NativeLayer == NativeLayer = True
  RuntimeLayer == RuntimeLayer = True
  LintLayer == LintLayer = True
  _ == _ = False

||| Whether an import is allowed by the layers, given the modules that are
||| ours. The runtime may import nothing that is not ours.
allowed : SortedSet String -> (importer : String) -> (imported : String) -> Maybe Bool
allowed ours importer imported = case layerOf importer of
  Nothing => Nothing
  Just RuntimeLayer => Just (contains imported ours && mayImport RuntimeLayer imported)
  Just l => if contains imported ours then Just (mayImport l imported) else Nothing
  where
    layerOf : String -> Maybe Layer
    layerOf m =
      if m == "Runtime" || isPrefixOf "Runtime." m then Just RuntimeLayer
      else if isPrefixOf "Compiler.Native." m then Just NativeLayer
      else if isPrefixOf "Flat." m then Just FlatLayer
      else if isPrefixOf "Lint." m then Just LintLayer
      else if isPrefixOf "Data." m then Just DataLayer
      else Nothing

    ||| The modules a layer may import: its own, and of the layers below it;
    ||| a module of no layer among ours (a program) by none, the data
    ||| structures nothing but data structures, and the runtime only what it
    ||| shares with the compiler: the heap-object model's modules, and
    ||| `Flat.Uniform`.
    mayImport : Layer -> String -> Bool
    mayImport DataLayer m = layerOf m == Just DataLayer
    mayImport FlatLayer m = layerOf m == Just DataLayer || layerOf m == Just FlatLayer
    mayImport NativeLayer m = maybe False (\l => l == DataLayer || l == FlatLayer || l == NativeLayer) (layerOf m)
    mayImport RuntimeLayer m = layerOf m == Just RuntimeLayer || isPrefixOf "Compiler.Native.HeapObject." m || m == "Flat.Uniform"
    mayImport LintLayer m = layerOf m == Just LintLayer

moduleOf : SourceFile -> String
moduleOf f = show f.mod.moduleNS

||| The modules defined by the files.
ourModules : List SourceFile -> SortedSet String
ourModules fs = fromList (map moduleOf fs)

||| `layering` and `syscall`: imports the layers do not allow, and the raw
||| system call imported outside the platforms' modules.
export
graphRules : List SourceFile -> List Finding
graphRules fs =
  let ours = ourModules fs in
  foldr (\f, rest => rules ours f ++ rest) [] fs
  where
    rules : SortedSet String -> SourceFile -> List Finding
    rules ours f =
      [ MkFinding "layering" f.path (fst (start i.loc)) (snd (start i.loc)) imported
          ("`" ++ moduleOf f ++ "` may not import `" ++ imported ++ "`: the layers")
      | i <- f.mod.imports, let imported = show i.path, allowed ours (moduleOf f) imported == Just False ]
      ++
      [ MkFinding "syscall" f.path (fst (start i.loc)) (snd (start i.loc)) "Runtime.OS.Syscall"
          "the raw system call outside `Runtime.OS`: the platform's services reach the system"
      | i <- f.mod.imports, show i.path == "Runtime.OS.Syscall", not (isPrefixOf "Runtime.OS." (moduleOf f)) ]
      where
        start : FC -> (Int, Int)
        start (MkFC _ s _) = s
        start (MkVirtualFC _ s _) = s
        start EmptyFC = (0, 0)

------------------------------------------------------------------------------
-- Groups and qualifiers
--
-- A module's group is its immediate parent component: `LocatedIR` for
-- `Compiler.Native.LocatedIR.Instr`. Names of two groups may be the same;
-- where they meet, a module qualifies one by its group, and one component
-- is all a qualifier ever needs.

||| A module's parent: its name without the last component.
parentOf : String -> Maybe String
parentOf m = case reverse (forget (Data.String.split (== '.') m)) of
  (_ :: rest@(_ :: _)) => Just (fastConcat (intersperse "." (reverse rest)))
  _ => Nothing

||| A module's group: the last component of its parent.
export
groupOf : String -> Maybe String
groupOf m = parentOf m >>= \p => last' (forget (Data.String.split (== '.') p))

||| `parent-unique`: no two of our groups have the same name, so that a
||| group's name, as a qualifier, means one group. Reported at a module of
||| each.
export
parentUnique : List SourceFile -> List Finding
parentUnique fs =
  let parents = the (SortedSet String) (fromList (mapMaybe (parentOf . moduleOf) fs))
      byName = foldl (\acc, p => let g = fromMaybe p (last' (forget (Data.String.split (== '.') p))) in
                                   insert g (p :: fromMaybe [] (lookup g acc)) acc)
                     (the (SortedMap String (List String)) empty) (Prelude.toList parents)
  in joined [ mapMaybe (report g ps) ps | (g, ps) <- SortedMap.toList byName, length ps > 1 ]
  where
    report : String -> List String -> String -> Maybe Finding
    report g ps p = case find (\f => parentOf (moduleOf f) == Just p) fs of
      Nothing => Nothing
      Just f => Just (MkFinding "parent-unique" f.path 0 0 g
                        ("the group `" ++ g ++ "` is also " ++ fastConcat (intersperse ", " (map (\o => "`" ++ o ++ "`") (filter (/= p) ps)))
                         ++ ": a group's name qualifies one group"))

||| `import-alias`: a module is imported under another name only as its
||| group, so that a qualifier is always a group's name; and a name of ours
||| is qualified by one component at most, its group, never by a group and
||| a module (`LocatedIR.Program.Program`): a module that must qualify a
||| name imports its module as its group.
export
importAlias : SortedSet String -> SourceFile -> List (FC, Name) -> List Finding
importAlias ours f refs =
  [ MkFinding "import-alias" f.path l c (show i.path)
      ("`" ++ show i.path ++ "` imported as `" ++ show i.nameAs ++ "`: a module is imported as its group, "
       ++ maybe "and this one has none" (\g => "`" ++ g ++ "`") (groupOf (show i.path)))
  | i <- f.mod.imports, show i.nameAs /= show i.path
  , groupOf (show i.path) /= Just (show i.nameAs)
  , let (l, c) = start i.loc ]
  ++
  mapMaybe deep refs
  where
    start : FC -> (Int, Int)
    start (MkFC _ s _) = s
    start (MkVirtualFC _ s _) = s
    start EmptyFC = (0, 0)

    -- the module of ours a qualifier names, if it names one
    ofOurs : String -> Maybe String
    ofOurs q = find (\m => m == q || isSuffixOf ("." ++ q) m) (Prelude.toList ours)

    report : FC -> (qualifier, name, m : String) -> Finding
    report fc q n m =
      let (l, c) = start fc
          g = fromMaybe m (groupOf m)
      in MkFinding "import-alias" f.path l c (q ++ "." ++ n)
           ("`" ++ q ++ "." ++ n ++ "` is qualified by more than its group: import `" ++ m
            ++ "` as `" ++ g ++ "` and write `" ++ g ++ "." ++ n ++ "`")

    deep : (FC, Name) -> Maybe Finding
    deep (fc, NS ns n) =
      let parts = reverse (unsafeUnfoldNamespace ns)
          q = fastConcat (intersperse "." parts)
      in if length parts < 2 then Nothing else map (report fc q (nameRoot n)) (ofOurs q)
    deep _ = Nothing

||| Names listed for a detail, the first few.
export
listed : List String -> String
listed ns =
  let shown = map (\n => "`" ++ n ++ "`") (take 6 ns)
      more = if length ns > 6 then [show (minus (length ns) 6) ++ " more"] else []
  in fastConcat (intersperse ", " (shown ++ more))

------------------------------------------------------------------------------
-- Names that meet

||| A name defined in several of our modules and seen together: the modules
||| that define it, and those where they meet.
public export
record Meeting where
  constructor MkMeeting
  name : String
  definers : List String
  inModules : List String

||| The modules whose names a module sees: those it imports, and those they
||| re-export publicly, in turn.
seen : SortedMap String (List String) -> SortedMap String (List String) -> String -> SortedSet String
seen imports reexports m = go empty (fromMaybe [] (lookup m imports))
  where
    go : SortedSet String -> List String -> SortedSet String
    go acc [] = acc
    go acc (i :: is) =
      if contains i acc then go acc is
      else go (insert i acc) (fromMaybe [] (lookup i reexports) ++ is)

||| The names that meet: a module's pool is its own names and those its
||| imports, and what they re-export publicly, make visible. Once imported a
||| name is unqualified, so two definitions of one name meet there whatever
||| their modules; they confuse a reader where the module writes the name
||| without a namespace, so only there do they count. Overloads of one
||| concept across types, each in a namespace named after its type, are not
||| two meanings, and do not count.
export
meetings : List (SourceFile, List Declared) -> List Meeting
meetings fds =
  let ours = ourModules (map fst fds)
      oursOnly = \is => filter (\i => contains i ours) is
      imports = fromList [ (moduleOf f, oursOnly (map (show . (.path)) f.mod.imports)) | (f, _) <- fds ]
      reexports = fromList [ (moduleOf f, oursOnly (map (show . (.path)) (filter (.reexport) f.mod.imports))) | (f, _) <- fds ]
      visibleIn = the (SortedMap String (List String)) (fromList [ (moduleOf f, joined (map (.visible) ds)) | (f, ds) <- fds ])
      found = foldl (\acc, fd => meet acc imports reexports visibleIn fd) empty fds
      overloads = the (SortedSet (String, String))
                    (fromList (joined [ map (moduleOf f,) (d.defines ++ d.visible) | (f, ds) <- fds, d <- ds, typedOverload d ]))
  in filter (\mt => not (exempt overloads mt.name mt.definers))
            (map (\(n, (ds, ms)) => MkMeeting n (Prelude.toList ds) (Prelude.toList ms)) (SortedMap.toList found))
  where
    exempt : SortedSet (String, String) -> String -> List String -> Bool
    exempt overloads n defs = all (\d => contains (d, n) overloads) defs

    tag : String -> List String -> List (String, String)
    tag m = map (\n => (n, m))

    meet : SortedMap String (SortedSet String, SortedSet String) -> SortedMap String (List String) -> SortedMap String (List String) ->
           SortedMap String (List String) -> (SourceFile, List Declared) -> SortedMap String (SortedSet String, SortedSet String)
    meet acc imports reexports visibleIn (f, ds) =
      let m = moduleOf f
          own = tag m (joined (map (.defines) ds))
          others = joined [ tag i (fromMaybe [] (lookup i visibleIn)) | i <- Prelude.toList (seen imports reexports m) ]
          written = the (SortedSet String) (fromList (joined (map (.bare) ds)))
          byName = foldl (\mp, (n, d) => if contains n written then insert n (insert d (fromMaybe empty (lookup n mp))) mp else mp)
                         (the (SortedMap String (SortedSet String)) empty) (own ++ others)
      in foldl (\a, (n, defs) => if length (Prelude.toList defs) < 2 then a
                                  else let (ds, ms) = fromMaybe (empty, empty) (lookup n a) in
                                       insert n (union ds defs, insert m ms) a)
               acc (SortedMap.toList byName)

||| `same-name`, a warning: one name, two meanings, written bare in a module
||| that sees both. Modules may define the same names; where they meet, a
||| module writes one qualified, importing its module as its group
||| (`import Compiler.Native.LocatedIR.Instr as LocatedIR`, `LocatedIR.Load`).
||| Each definition is reported, with the others and where they meet.
export
sameName : List (SourceFile, List Declared) -> List Finding
sameName fds = joined (map report (meetings fds))
  where
    at : String -> String -> Maybe (SourceFile, Declared)
    at m n = case find (\fd => moduleOf (fst fd) == m) fds of
      Nothing => Nothing
      Just (f, ds) => map (f,) (find (\d => (n `elem` d.defines) || (n `elem` d.visible)) ds)

    start : FC -> (Int, Int)
    start (MkFC _ s _) = s
    start (MkVirtualFC _ s _) = s
    start EmptyFC = (0, 0)

    report : Meeting -> List Finding
    report mt = mapMaybe one mt.definers
      where
        one : String -> Maybe Finding
        one d = case at d mt.name of
          Nothing => Nothing
          Just (f, decl) =>
            let (l, c) = start decl.decl.fc
                others = filter (/= d) mt.definers
            in Just (MkFinding "same-name" f.path l c mt.name
                      ("`" ++ mt.name ++ "` is also defined in " ++ fastConcat (intersperse ", " (map (\o => "`" ++ o ++ "`") others))
                       ++ "; they meet bare in " ++ listed mt.inModules
                       ++ (case mt.inModules of [_] => ", which qualifies"; _ => ", each of which qualifies") ++ " one by its group"))

------------------------------------------------------------------------------
-- Health

||| A share as a whole percentage; 100 when there is nothing to count.
export
percent : Nat -> Nat -> Nat
percent _ Z = 100
percent k n = let k' = the Integer (cast k); n' = the Integer (cast n) in
              cast ((200 * k' + n') `div` (2 * n'))

||| What costs a component of the score, for a reader looking for what to
||| change: what it is about (a module, an import, a definition), what it
||| costs, in the units the component counts, and what the cost is made of.
public export
record Offender where
  constructor MkOffender
  subject : String
  cost : Nat
  detail : String

||| One component of the score: its group, its name, its value, what it
||| counts, and its offenders.
public export
record Component where
  constructor MkComponent
  group : String
  name : String
  value : Nat
  counted : String
  offenders : List Offender

||| A module left out of a component of the score, by a comment of its own,
||| `-- lint: exclude <component>: <reason>`: the component, the reason, and
||| where the comment is. Only precision leaves modules out, as imported
||| ones: a module whose names are offered in bulk until its importers are
||| reshaped. The score names what it leaves out.
public export
record Exclusion where
  constructor MkExclusion
  componentName : String
  reason : String
  line : Int
  col : Int

||| The components a module may be left out of.
export
excludable : List String
excludable = ["precision"]

||| A file's exclusions, as its comments write them.
export
exclusions : SourceFile -> List Exclusion
exclusions f = mapMaybe one f.comments
  where
    one : SourceComment -> Maybe Exclusion
    one c =
      if c.isDoc || not (isPrefixOf "lint: exclude " c.text) then Nothing else
        let rest = substr 14 (length c.text) c.text
            (comp, why) = break (== ':') rest
        in Just (MkExclusion (trim comp) (trim (substr 1 (length why) why)) c.line c.col)

||| `exclusion`: an exclusion of no component that leaves modules out, or
||| without a reason.
export
exclusionRules : SourceFile -> List Finding
exclusionRules f = mapMaybe check (exclusions f)
  where
    check : Exclusion -> Maybe Finding
    check e =
      let at = MkFinding "exclusion" f.path e.line e.col e.componentName in
      if not (e.componentName `elem` excludable) then Just (at ("no component `" ++ e.componentName ++ "` leaves modules out"))
      else if e.reason == "" then Just (at ("an exclusion from `" ++ e.componentName ++ "` says why"))
      else Nothing

||| The components of the architectural health of the files' modules, in
||| their groups: structure (the import graph), readability (what a reader
||| reading linearly meets), each with its offenders.
|||
||| Each component is a function of its own, with a short `let`: in one long
||| `let`, each binding that passes a lambda or a polymorphic function to
||| `map` or `filter` creates metavariables that carry every binding before
||| it, and typechecking costs exponentially in the length of the chain.
export
health : List (SourceFile, List Declared) -> List Component
health fds =
  let fs = map fst fds in
  [ encapsulation fs, layering fs, coupling fs, cohesion, names, uniqueness, scoping ]
  where
    directive : PDecl -> Bool
    directive d = case d.val of
      PDirective _ => True
      _ => False

    encapsulation : List SourceFile -> Component
    encapsulation fs =
      let notFacades = filter (\f => not (all directive f.mod.decls)) fs
          imports = joined (map (\f => f.mod.imports) notFacades)
          privates = length (filter (not . (.reexport)) imports)
      in MkComponent "structure" "encapsulation" (percent privates (length imports))
           ("private imports, façades exempt: " ++ show privates ++ " of " ++ show (length imports))
           [ MkOffender (moduleOf f) (length pub) ("imports publicly " ++ listed pub)
           | f <- notFacades, let pub = [ show i.path | i <- f.mod.imports, i.reexport ], not (null pub) ]

    -- an import with whether the layers allow it
    allowedImport : (SourceFile, Import, Bool) -> Bool
    allowedImport (_, _, ok) = ok

    disallowed : (SourceFile, Import, Bool) -> Offender
    disallowed (f, i, _) = MkOffender (moduleOf f) 1 ("imports `" ++ show i.path ++ "`, which its layer may not")

    layering : List SourceFile -> Component
    layering fs =
      let ours = ourModules fs
          checked = joined [ mapMaybe (\i => map (f, i,) (allowed ours (moduleOf f) (show i.path))) f.mod.imports | f <- fs ]
          good = length (filter allowedImport checked)
      in MkComponent "structure" "layering" (percent good (length checked))
           ("imports the layers allow: " ++ show good ++ " of " ++ show (length checked))
           (map disallowed (filter (not . allowedImport) checked))

    reaching : (ourCount : Nat) -> (String, List String) -> Offender
    reaching ourCount (m, r) = MkOffender m (length r) ("its imports reach " ++ show (length r) ++ " of our " ++ show ourCount ++ " modules")

    ||| The modules each module's imports reach, ours only.
    reaches : SortedMap String (List String) -> String -> SortedSet String
    reaches g m = go empty (fromMaybe [] (lookup m g))
      where
        go : SortedSet String -> List String -> SortedSet String
        go seen [] = seen
        go seen (n :: ns) =
          if contains n seen then go seen ns
          else go (insert n seen) (fromMaybe [] (lookup n g) ++ ns)

    coupling : List SourceFile -> Component
    coupling fs =
      let ours = ourModules fs
          g = the (SortedMap String (List String)) (fromList [ (moduleOf f, [ show i.path | i <- f.mod.imports, contains (show i.path) ours ]) | f <- fs ])
          n = length fs
          reachOf = [ (moduleOf f, Prelude.toList (reaches g (moduleOf f))) | f <- fs ]
          reached = sum (map (\mr => length (snd mr)) reachOf)
      in MkComponent "structure" "coupling" (percent (n * n `minus` reached) (n * n))
           ("module pairs a change cannot reach: " ++ show (n * n `minus` reached) ++ " of " ++ show (n * n))
           (map (reaching n) reachOf)

    cohesion : Component
    cohesion =
      let adjacencies = joined (map (\fd => adjacency (snd fd)) fds)
          adjacent = length (filter (\a => isNothing a.intruder) adjacencies)
      in MkComponent "readability" "cohesion" (percent adjacent (length adjacencies))
           ("implementations next to their types: " ++ show adjacent ++ " of " ++ show (length adjacencies))
           [ MkOffender (maybe "" fst a.impl.implementing ++ " " ++ a.type) 1 ("apart from `" ++ a.type ++ "`")
           | a <- adjacencies, isJust a.intruder ]

    unnamedModule : (SourceFile, List Declared) -> Offender
    unnamedModule (f, ds) = MkOffender (moduleOf f) 1 ("defines " ++ listed (joined (map (.visible) ds)))

    names : Component
    names =
      let n = length fds
          unnamed = filter (\fd => not (namedAfterSymbol (fst fd) (snd fd))) fds
      in MkComponent "readability" "names" (percent (minus n (length unnamed)) n)
           ("modules named after a symbol they define: " ++ show (minus n (length unnamed)) ++ " of " ++ show n)
           (map unnamedModule unnamed)

    -- the names a module exports, each with the module
    exportsOf : (SourceFile, List Declared) -> List (String, String)
    exportsOf (f, ds) = map (\n => (n, moduleOf f)) (joined (map (.visible) ds))

    uniqueness : Component
    uniqueness =
      let exportedNames = joined (map exportsOf fds)
          ms = meetings fds
          meetingNames = map (.name) ms
          unique = length (filter (\nm => not (fst nm `elem` meetingNames)) exportedNames)
      in MkComponent "readability" "uniqueness" (percent unique (length exportedNames))
           ("exported names never written bare where another of the name is seen: " ++ show unique ++ " of " ++ show (length exportedNames))
           [ MkOffender mt.name (length (filter (\nm => fst nm == mt.name) exportedNames))
               ("defined in " ++ listed mt.definers ++ "; they meet bare in " ++ listed mt.inModules)
           | mt <- ms ]

    moduleWide : (SourceFile, (List (Declared, Declared), Nat)) -> Maybe Offender
    moduleWide (_, ([], _)) = Nothing
    moduleWide (f, (s, _)) = Just (MkOffender (moduleOf f) (length s) ("module-wide, each used by one: " ++ listed (joined (map (\hu => (fst hu).defines) s))))

    scoping : Component
    scoping =
      let perModule = map (\fd => (fst fd, helpers (snd fd))) fds
          single = sum (map (\pm => length (fst (snd pm))) perModule)
          scoped = sum (map (\pm => snd (snd pm)) perModule)
      in MkComponent "readability" "scoping" (percent scoped (scoped + single))
           ("helpers local to a function or a namespace block, of those and the ones a single user leaves module-wide: "
            ++ show scoped ++ " of " ++ show (scoped + single))
           (mapMaybe moduleWide perModule)

||| The groups of the components, in the order they first appear.
export
groups : List Component -> List String
groups = foldl (\gs, c => if c.group `elem` gs then gs else gs ++ [c.group]) []

||| A group's score: the mean of its components.
export
groupScore : List Component -> String -> Nat
groupScore cs g = let mine = filter (\c => c.group == g) cs in percent (sum (map (.value) mine)) (100 * length mine)

||| The score: the mean of the groups' scores.
export
score : List Component -> Nat
score cs = case groups cs of
  [] => 100
  gs => percent (sum (map (groupScore cs) gs)) (100 * length gs)
