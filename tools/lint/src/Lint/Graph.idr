||| The import graph of the modules linted together: the rules over it, and
||| the architectural health score.
|||
||| A module's layer is told by its name. Of our modules, a layer imports only
||| those of the layers below it; a module of no layer (a program, a test) may
||| import any. The runtime imports nothing from the libraries but what it
||| shares with the compiler.
module Lint.Graph

import Data.List
import Data.SortedMap
import Data.SortedSet
import Data.String
import Idris.Syntax
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

layerOf : String -> Maybe Layer
layerOf m =
  if m == "Runtime" || isPrefixOf "Runtime." m then Just RuntimeLayer
  else if isPrefixOf "Compiler.Native." m then Just NativeLayer
  else if isPrefixOf "Flat." m then Just FlatLayer
  else if isPrefixOf "Lint." m then Just LintLayer
  else if isPrefixOf "Data." m then Just DataLayer
  else Nothing

||| The modules of other layers that a layer may import: a module of no layer
||| among ours (a program) by none, and the runtime only the two modules it
||| shares with the compiler.
mayImport : Layer -> String -> Bool
mayImport DataLayer m = False
mayImport FlatLayer m = layerOf m == Just DataLayer || layerOf m == Just FlatLayer
mayImport NativeLayer m = maybe False (\l => l == DataLayer || l == FlatLayer || l == NativeLayer) (layerOf m)
mayImport RuntimeLayer m = layerOf m == Just RuntimeLayer || m == "Compiler.Native.HeapObject" || m == "Flat.Uniform"
mayImport LintLayer m = layerOf m == Just LintLayer

||| Whether an import is allowed by the layers, given the modules that are
||| ours. The runtime may import nothing that is not ours.
allowed : SortedSet String -> (importer : String) -> (imported : String) -> Maybe Bool
allowed ours importer imported = case layerOf importer of
  Nothing => Nothing
  Just RuntimeLayer => Just (contains imported ours && mayImport RuntimeLayer imported)
  Just l => if contains imported ours then Just (mayImport l imported) else Nothing

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
-- Names that meet

||| A name defined in several of our modules and seen together in one: the
||| modules that define it, and one where they meet.
public export
record Meeting where
  constructor MkMeeting
  name : String
  definers : List String
  inModule : String

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
  in filter (\mt => not (exempt overloads mt.name mt.definers)) (map (\(n, (ds, m)) => MkMeeting n ds m) (SortedMap.toList found))
  where
    exempt : SortedSet (String, String) -> String -> List String -> Bool
    exempt overloads n defs = all (\d => contains (d, n) overloads) defs

    tag : String -> List String -> List (String, String)
    tag m = map (\n => (n, m))

    meet : SortedMap String (List String, String) -> SortedMap String (List String) -> SortedMap String (List String) ->
           SortedMap String (List String) -> (SourceFile, List Declared) -> SortedMap String (List String, String)
    meet acc imports reexports visibleIn (f, ds) =
      let m = moduleOf f
          own = tag m (joined (map (.defines) ds))
          others = joined [ tag i (fromMaybe [] (lookup i visibleIn)) | i <- Prelude.toList (seen imports reexports m) ]
          written = the (SortedSet String) (fromList (joined (map (.bare) ds)))
          byName = foldl (\mp, (n, d) => if contains n written then insert n (insert d (fromMaybe empty (lookup n mp))) mp else mp)
                         (the (SortedMap String (SortedSet String)) empty) (own ++ others)
      in foldl (\a, (n, defs) => let ds' = Prelude.toList defs in
                                   if length ds' < 2 || isJust (lookup n a) then a else insert n (ds', m) a)
               acc (SortedMap.toList byName)

||| `same-name`, a warning: one name, two meanings, meeting in a module: each
||| definition is reported, with the others and where they meet.
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
                       ++ "; they meet in `" ++ mt.inModule ++ "`"))

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

||| Names listed for a detail, the first few.
export
listed : List String -> String
listed ns =
  let shown = map (\n => "`" ++ n ++ "`") (take 6 ns)
      more = if length ns > 6 then [show (minus (length ns) 6) ++ " more"] else []
  in fastConcat (intersperse ", " (shown ++ more))

||| The modules each module's imports reach, ours only.
reaches : SortedMap String (List String) -> String -> SortedSet String
reaches g m = go empty (fromMaybe [] (lookup m g))
  where
    go : SortedSet String -> List String -> SortedSet String
    go seen [] = seen
    go seen (n :: ns) =
      if contains n seen then go seen ns
      else go (insert n seen) (fromMaybe [] (lookup n g) ++ ns)

||| Of what our modules import from each other, how much they use, import
||| by import: the importer, the imported module, the names the import
||| makes visible (the module's own and its public re-exports') that the
||| importer mentions, and all of them. Weighted by size, so that a large
||| bundle imported for a few names costs more than a small module.
precision : List (SourceFile, List Declared) -> List (String, String, Nat, Nat)
precision fds =
  let ours = ourModules (map fst fds)
      visibleIn = the (SortedMap String (List String)) (fromList [ (moduleOf f, joined (map (.visible) ds)) | (f, ds) <- fds ])
      reexports = the (SortedMap String (List String))
                    (fromList [ (moduleOf f, filter (\i => contains i ours) (map (show . (.path)) (filter (.reexport) f.mod.imports))) | (f, _) <- fds ])
      edges = joined [ map (f, ds,) (filter (\i => contains i ours) (map (show . (.path)) f.mod.imports)) | (f, ds) <- fds ]
  in map (edge visibleIn reexports) edges
  where
    exposed : SortedMap String (List String) -> String -> SortedSet String
    exposed reexports b = go (singleton b) (fromMaybe [] (lookup b reexports))
      where
        go : SortedSet String -> List String -> SortedSet String
        go acc [] = acc
        go acc (i :: is) = if contains i acc then go acc is else go (insert i acc) (fromMaybe [] (lookup i reexports) ++ is)

    edge : SortedMap String (List String) -> SortedMap String (List String) ->
           (SourceFile, List Declared, String) -> (String, String, Nat, Nat)
    edge visibleIn reexports (f, ds, b) =
      let names = the (SortedSet String) (fromList (joined (map (\m => fromMaybe [] (lookup m visibleIn)) (Prelude.toList (exposed reexports b)))))
          mentioned = the (SortedSet String) (fromList (joined (map (.mentions) ds)))
          used = length (filter (\n => contains n mentioned) (Prelude.toList names))
      in (moduleOf f, b, used, length (Prelude.toList names))

||| The offenders of precision: each imported module, by the names its
||| importers leave unused, with the importers that use the fewest.
precisionOffenders : List (String, String, Nat, Nat) -> List Offender
precisionOffenders edges =
  let byImported = foldl (\acc, (a, b, u, o) => insert b ((a, u, o) :: fromMaybe [] (lookup b acc)) acc)
                         (the (SortedMap String (List (String, Nat, Nat))) empty) edges
  in map offender (SortedMap.toList byImported)
  where
    offender : (String, List (String, Nat, Nat)) -> Offender
    offender (b, importers) =
      let offered = foldl (\m, (_, _, o) => max m o) (the Nat 0) importers
          unused = sum (map (\(_, u, o) => minus o u) importers)
          fewest = sortBy (\(_, u, _), (_, v, _) => compare u v) importers
      in MkOffender b unused
           (show (length importers) ++ (if length importers == 1 then " importer" else " importers") ++ " of its " ++ show offered ++ " names; fewest used: "
            ++ fastConcat (intersperse ", " (map (\(a, u, _) => a ++ " " ++ show u) (take 4 fewest))))

||| The components of the architectural health of the files' modules, in
||| their groups: structure (the import graph), readability (what a reader
||| reading linearly meets), each with its offenders.
export
health : List (SourceFile, List Declared) -> List Component
health fds =
  let fs = map fst fds in
  let ours = ourModules fs
      notFacades = filter (\f => not (all directive f.mod.decls)) fs
      imports = foldr (\f, rest => f.mod.imports ++ rest) [] notFacades
      privates = length (filter (not . (.reexport)) imports)
      checked = joined [ mapMaybe (\i => map (f, i,) (allowed ours (moduleOf f) (show i.path))) f.mod.imports | f <- fs ]
      good = length (filter (\(_, _, ok) => ok) checked)
      g = fromList [ (moduleOf f, [ show i.path | i <- f.mod.imports, contains (show i.path) ours ]) | f <- fs ]
      n = length fs
      reachOf = [ (moduleOf f, Prelude.toList (reaches g (moduleOf f))) | f <- fs ]
      reached = sum (map (\(_, r) => length r) reachOf)
      adjacencies = foldr (\(_, ds), rest => adjacency ds ++ rest) (the (List Adjacency) []) fds
      adjacent = length (filter (\a => isNothing a.intruder) adjacencies)
      unnamed = filter (\fd => not (namedAfterSymbol (fst fd) (snd fd))) fds
      exportedNames = foldr (\(f, ds), rest => map (\n => (n, moduleOf f)) (joined (map (.visible) ds)) ++ rest) (the (List (String, String)) []) fds
      ms = meetings fds
      meetingNames = map (.name) ms
      unique = length (filter (\nm => not (fst nm `elem` meetingNames)) exportedNames)
      edges = precision fds
      usedNames = sum (map (\(_, _, u, _) => u) edges)
      offered = sum (map (\(_, _, _, o) => o) edges)
      perModuleHelpers = map (\(f, ds) => (f, helpers ds)) fds
      single = sum (map (\(_, (s, _)) => length s) perModuleHelpers)
      scopedHelpers = sum (map (\(_, (_, c)) => c) perModuleHelpers)
  in [ MkComponent "structure" "encapsulation" (percent privates (length imports))
         ("private imports, façades exempt: " ++ show privates ++ " of " ++ show (length imports))
         [ MkOffender (moduleOf f) (length pub) ("imports publicly " ++ listed pub)
         | f <- notFacades, let pub = [ show i.path | i <- f.mod.imports, i.reexport ], not (null pub) ]
     , MkComponent "structure" "layering" (percent good (length checked))
         ("imports the layers allow: " ++ show good ++ " of " ++ show (length checked))
         [ MkOffender (moduleOf f) 1 ("imports `" ++ show i.path ++ "`, which its layer may not") | (f, i, ok) <- checked, not ok ]
     , MkComponent "structure" "coupling" (percent (n * n `minus` reached) (n * n))
         ("module pairs a change cannot reach: " ++ show (n * n `minus` reached) ++ " of " ++ show (n * n))
         [ MkOffender m (length r) ("its imports reach " ++ show (length r) ++ " of our " ++ show n ++ " modules") | (m, r) <- reachOf ]
     , MkComponent "structure" "precision" (percent usedNames offered)
         ("imported names a module uses: " ++ show usedNames ++ " of " ++ show offered)
         (precisionOffenders edges)
     , MkComponent "readability" "cohesion" (percent adjacent (length adjacencies))
         ("implementations next to their types: " ++ show adjacent ++ " of " ++ show (length adjacencies))
         [ MkOffender (maybe "" fst a.impl.implementing ++ " " ++ a.type) 1 ("apart from `" ++ a.type ++ "`")
         | a <- adjacencies, isJust a.intruder ]
     , MkComponent "readability" "names" (percent (minus n (length unnamed)) n)
         ("modules named after a symbol they define: " ++ show (minus n (length unnamed)) ++ " of " ++ show n)
         [ MkOffender (moduleOf f) 1 ("defines " ++ listed (joined (map (.visible) ds))) | (f, ds) <- unnamed ]
     , MkComponent "readability" "uniqueness" (percent unique (length exportedNames))
         ("exported names that meet no other definition: " ++ show unique ++ " of " ++ show (length exportedNames))
         [ MkOffender mt.name (length (filter (\nm => fst nm == mt.name) exportedNames))
             ("defined in " ++ listed mt.definers ++ "; they meet in `" ++ mt.inModule ++ "`")
         | mt <- ms ]
     , MkComponent "readability" "scoping" (percent scopedHelpers (scopedHelpers + single))
         ("helpers local to a function or a namespace block, of those and the ones a single user leaves module-wide: "
          ++ show scopedHelpers ++ " of " ++ show (scopedHelpers + single))
         [ MkOffender (moduleOf f) (length s) ("module-wide, each used by one: " ++ listed (joined (map (\(h, _) => h.defines) s)))
         | (f, (s, _)) <- perModuleHelpers, not (null s) ] ]
  where
    directive : PDecl -> Bool
    directive d = case d.val of
      PDirective _ => True
      _ => False

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
