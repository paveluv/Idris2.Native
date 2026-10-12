||| The rules over what our modules use, resolved from their TTCs, and the
||| components of the health score they measure.
|||
||| A module imports what it uses: an import none of whose names the module
||| uses is a finding, and so is a module used but reached only through
||| another of ours re-exporting it. What the packages' modules re-export is
||| their own design, and a façade of ours re-exports by design: a module
||| reached through those is reached as meant.
module Lint.ResolvedRules

import Core.FC
import Data.List
import Data.SortedMap
import Data.SortedSet
import Data.String
import Idris.Syntax
import Lint.Finding
import Lint.Graph
import Lint.Resolution
import Lint.Rules
import Lint.Source

%default covering

||| What a module makes visible to its importers: itself, and what it
||| re-exports publicly, in turn, re-exports followed where `follow` says.
visibleThrough : SortedMap String (List (String, Bool)) -> (follow : String -> Bool) -> String -> SortedSet String
visibleThrough imports follow m = go empty [m]
  where
    go : SortedSet String -> List String -> SortedSet String
    go acc [] = acc
    go acc (i :: is) =
      if contains i acc then go acc is
      else let next = if follow i then map (\(j, _) => j) (filter (\(_, reexported) => reexported) (fromMaybe [] (lookup i imports))) else [] in
           go (insert i acc) (next ++ is)

||| One of our modules with what its text writes and what it uses, as the
||| rules over it see it.
record Linted where
  constructor MkLinted
  file : SourceFile
  resolved : ResolvedModule
  ||| The other modules whose names the module's text writes, or whose
  ||| implementations it uses, found by search, each with the names.
  writtenUses : SortedMap String (List String)
  ||| The modules its imports reach as meant: through the packages'
  ||| re-exports and our façades', not those of our other modules; the
  ||| implicit `Prelude` included.
  reached : SortedSet String
  ||| Its private imports, each with whether it is used: whether the module
  ||| refers to anything it makes visible, written or not (a type an
  ||| implicit argument names, an implementation found by search).
  privateImports : List (Import, Bool)

||| Our modules, each with its file and what it writes.
modulesOf : List (SourceFile, Mentions) -> Resolution -> List Linted
modulesOf fms r =
  let byPath = the (SortedMap String ResolvedModule) (fromList (map (\rm => (rm.path, rm)) r.modules))
      -- our modules whose re-exports a module may not lean on: all but the
      -- façades
      leanedOn = the (SortedSet String) (fromList [ show f.mod.moduleNS | (f, _) <- fms, not (facade f) ])
  in mapMaybe (one byPath leanedOn) fms
  where
    one : SortedMap String ResolvedModule -> SortedSet String -> (SourceFile, Mentions) -> Maybe Linted
    one byPath leanedOn (f, ms) = case lookup f.path byPath of
      Nothing => Nothing
      Just rm =>
        let written = the (SortedSet String) (fromList (map (\(_, n) => nameRoot n) ms.refs))
            ws = foldl (\acc, u => if u.searched || contains u.name written then insert u.definer (u.name :: fromMaybe [] (lookup u.definer acc)) acc else acc)
                       empty rm.uses
            used = the (SortedSet String) (fromList (map (.definer) rm.uses))
            reached = foldl Data.SortedSet.union empty
                            (map (\(i, _) => visibleThrough r.importsOf (\m => not (contains m leanedOn)) i) rm.imports)
            privates = [ (i, any (\v => contains v used) (Prelude.toList (visibleThrough r.importsOf (const True) (show i.path))))
                       | i <- f.mod.imports, not i.reexport ]
        in Just (MkLinted f rm ws reached privates)

------------------------------------------------------------------------------
-- The rules

||| `import-unused`: a private import none of whose names the module uses,
||| neither the module's own nor any it re-exports. A façade's imports are
||| for its importers, and so is a public import: neither is reported.
importUnused : Linted -> List Finding
importUnused m =
  if facade m.file then [] else
    [ finding m.file "import-unused" i.loc (show i.path)
        ("`" ++ show i.path ++ "` is imported, and nothing it makes visible is used")
    | i <- map (\(i, _) => i) (filter (\(_, isUsed) => not isUsed) m.privateImports) ]

||| `import-indirect`: a module whose names the module writes, or whose
||| implementations it uses, reached only through one of our modules
||| re-exporting it. Search finds an implementation only where its module
||| is visible, so a module that uses one imports its module, as it does
||| one whose names it writes.
importIndirect : Resolution -> Linted -> List Finding
importIndirect r m = mapMaybe report (SortedMap.toList m.writtenUses)
  where
    through : String -> Maybe Import
    through u = find (\i => contains u (visibleThrough r.importsOf (const True) (show i.path))) m.file.mod.imports

    report : (String, List String) -> Maybe Finding
    report (u, ns) =
      if contains u m.reached then Nothing else
        let names = fastConcat (intersperse ", " (map (\n => "`" ++ n ++ "`") (take 3 (nub ns))))
            via = through u
            how = maybe "without importing it" (\i => "only through `" ++ show i.path ++ "`") via
        in Just (finding m.file "import-indirect" (maybe EmptyFC (.loc) via) u
                   ("`" ++ u ++ "` is used (" ++ names ++ ") " ++ how ++ ": import it"))

||| `list-append`, a warning: a definition that joins lists, by `++` or by a
||| list's semigroup or monoid; a `Builder` joins in constant time.
listAppend : Linted -> List Finding
listAppend m =
  [ MkFinding "list-append" m.file.path a.line a.col a.subject
      ("`" ++ a.subject ++ "` joins lists " ++ times a.lists ++ ": a `Builder` joins in constant time")
  | a <- m.resolved.appends, a.lists > 0 ]
  where
    times : Nat -> String
    times 1 = "once"
    times 2 = "twice"
    times k = show k ++ " times"

||| The rules over the program resolved.
export
resolvedRules : List (SourceFile, Mentions) -> Resolution -> List Finding
resolvedRules fms r =
  joined [ importUnused m ++ importIndirect r m ++ listAppend m | m <- modulesOf fms r ]

------------------------------------------------------------------------------
-- Health

||| The components the resolution measures: of the other modules whose names
||| our modules write, the share imported directly (or through a façade or a
||| package); of the private imports, the share used; and of the appends,
||| the share that join builders.
export
resolvedHealth : List (SourceFile, Mentions) -> Resolution -> List Component
resolvedHealth fms r =
  let ms = modulesOf fms r
      pairs = joined [ map (m,) (keys m.writtenUses) | m <- ms ]
      direct = length (filter (\(m, u) => contains u m.reached) pairs)
      imports = joined [ m.privateImports | m <- ms, not (facade m.file) ]
      used = length (filter (\(_, isUsed) => isUsed) imports)
      lists = sum [ a.lists | m <- ms, a <- m.resolved.appends ]
      builders = sum [ a.builders | m <- ms, a <- m.resolved.appends ]
  in [ MkComponent "structure" "directness" (percent direct (length pairs))
         ("modules used that are imported directly: " ++ show direct ++ " of " ++ show (length pairs))
     , MkComponent "structure" "leanness" (percent used (length imports))
         ("private imports used: " ++ show used ++ " of " ++ show (length imports))
     , MkComponent "efficiency" "builders" (percent builders (lists + builders))
         ("appends that join builders: " ++ show builders ++ " of " ++ show (lists + builders)) ]
