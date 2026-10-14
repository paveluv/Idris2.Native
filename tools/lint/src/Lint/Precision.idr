||| How precisely our modules import each other (`precision`): of the
||| concepts an import offers, the share the importer uses.
|||
||| A module is imported for some of its concepts (`Lint.Concept`); the
||| others are what the importer reads past, recompiles for and is coupled
||| to without needing them. An import offers the concepts the imported
||| module exports, and those of the modules it re-exports in turn; the
||| importer uses a concept if it refers to any of its names, resolved:
||| a constructor in a pattern, a field, a method, an implementation found
||| by search. Each concept counts once, whatever its size, and the score
||| sums over every import between our modules, so that a module imported
||| for a few of many concepts weighs more than a small one. A module may
||| leave itself out, as an imported one, by a reason
||| (`-- lint: exclude precision: ...`).
module Lint.Precision

import Lint.Concept
import Lint.Finding
import Lint.Graph
import Lint.Resolution
import Lint.Rules
import Lint.Source

import Core.Name.Namespace
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Idris.Syntax

%default covering

||| An import between our modules, as precision counts it: the importer,
||| the module imported, the concepts it offers, and those of them the
||| importer uses.
record ImportEdge where
  constructor MkImportEdge
  importer : String
  imported : String
  offered : Nat
  used : Nat

||| The modules left out of a component, each by a comment with its reason.
export
excludedFrom : (component : String) -> List SourceFile -> List String
excludedFrom c fs = [ show f.mod.moduleNS | f <- fs, any (\e => e.componentName == c && e.reason /= "") (exclusions f) ]

||| The concepts of each of our modules, by module.
export
conceptsByModule : List (SourceFile, List Declared) -> SortedMap String (List Concept)
conceptsByModule fds = fromList [ (show f.mod.moduleNS, conceptsOf f ds) | (f, ds) <- fds ]

||| The concepts of a module a module uses, by name.
export
usedOf : SortedMap String (List Concept) -> ResolvedModule -> (definer : String) -> SortedSet String
usedOf byModule rm m =
  let cs = fromMaybe [] (lookup m byModule) in
  fromList (mapMaybe (\u => if u.definer == m then conceptOfUse cs u.name u.searched else Nothing) rm.uses)

||| `precision`: of the concepts our modules' imports of each other offer,
||| the share the importers use; its offenders, each imported module by the
||| concepts its importers leave unused, with those that use the fewest.
export
precision : List (SourceFile, List Declared) -> Resolution -> Component
precision fds r =
  let byModule = conceptsByModule fds
      out = excludedFrom "precision" (map fst fds)
      ours = the (SortedSet String) (fromList (keys byModule))
      edges = joined [ mapMaybe (edge byModule ours out rm) (map fst rm.imports) | rm <- r.modules ]
      usedNames = sum (map (.used) edges)
      offeredNames = sum (map (.offered) edges)
  in MkComponent "structure" "precision" (percent usedNames offeredNames)
       ("imported concepts a module uses: " ++ show usedNames ++ " of " ++ show offeredNames ++ leftOut out)
       (offenders byModule edges)
  where
    leftOut : List String -> String
    leftOut [] = ""
    leftOut ms = "; left out: " ++ listed ms

    -- an import of one of ours, with what it offers through its re-exports
    edge : SortedMap String (List Concept) -> SortedSet String -> List String -> ResolvedModule -> String -> Maybe ImportEdge
    edge byModule ours out rm i =
      if not (contains i ours) || (i `elem` out) then Nothing else
        let exposed = filter (shown ours out) (Prelude.toList (visibleThrough r.importsOf (`contains` ours) i)) in
        Just (MkImportEdge rm.name i (sum (map (length . offeredIn byModule) exposed)) (sum (map (usedIn byModule rm) exposed)))
      where
        shown : SortedSet String -> List String -> String -> Bool
        shown ours out m = contains m ours && not (m `elem` out)

        offeredIn : SortedMap String (List Concept) -> String -> List Concept
        offeredIn byModule m = filter (.offered) (fromMaybe [] (lookup m byModule))

        usedIn : SortedMap String (List Concept) -> ResolvedModule -> String -> Nat
        usedIn byModule rm m = let used = usedOf byModule rm m in length (filter (\c => contains c.name used) (offeredIn byModule m))

    offenders : SortedMap String (List Concept) -> List ImportEdge -> List Offender
    offenders byModule edges =
      let byImported = foldl (\acc, e => insert e.imported (e :: fromMaybe [] (lookup e.imported acc)) acc)
                             (the (SortedMap String (List ImportEdge)) empty) edges
      in filter (\o => o.cost > 0) (map offender (SortedMap.toList byImported))
      where
        offender : (String, List ImportEdge) -> Offender
        offender (b, importers) =
          let concepts = filter (.offered) (fromMaybe [] (lookup b byModule))
              unused = sum (map (\e => minus e.offered e.used) importers)
              fewest = sortBy (\e, e' => compare e.used e'.used) importers
          in MkOffender b unused
               (show (length importers) ++ (if length importers == 1 then " importer" else " importers") ++ " of its "
                ++ show (length concepts) ++ (if length concepts == 1 then " concept (" else " concepts (") ++ listed (map (.name) (take 6 concepts))
                ++ (if length concepts > 6 then ", ..." else "") ++ "); fewest used: "
                ++ fastConcat (intersperse ", " (map (\e => e.importer ++ " " ++ show e.used) (take 4 fewest))))
