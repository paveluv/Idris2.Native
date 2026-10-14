||| How far each group of modules is split apart (`distinction`): siblings
||| that the same modules always import together could be one module, and
||| a group most of whose members could be joined so is oversplit.
|||
||| A group is the modules under one parent (`Compiler.Native.IRCommon.
||| Operators`' `ConvOp`, `FOp`, ...); modules at the top are in none. Two
||| members with the same importers, at least two, are imported together
||| every time: no importer takes one without the other, so joining them
||| would cost none of them precision. One importer is no evidence: a module
||| imported once is imported with whatever else its importer needs. A
||| group's share of members that could be joined so says how oversplit it
||| is; at four in five or more, the group is a candidate to collapse into
||| one module.
module Lint.Distinction

import Core.Name.Namespace
import Data.List
import Data.List1
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Data.String
import Idris.Syntax
import Lint.Finding
import Lint.Graph
import Lint.Source

%default covering

||| `distinction`: of the members of our groups, the share imported apart
||| from every sibling. Its offenders, each group with members that could
||| be joined, by the modules joining would remove: what share of the group
||| that is, and which siblings are always imported together, by whom.
export
distinction : List SourceFile -> Component
distinction fs =
  let members = filter (\m => groupOf m /= "") (map name fs)
      classes = twinClasses importedTwice
      joinable = length (joined classes)
  in MkComponent "structure" "distinction" (percent (minus (length members) joinable) (length members))
       ("group members imported apart from their siblings: " ++ show (minus (length members) joinable) ++ " of " ++ show (length members))
       (mapMaybe (groupOffender members classes) (nub (map groupOf members)))
  where
    name : SourceFile -> String
    name f = show f.mod.moduleNS

    addImporter : SortedMap String (List String) -> (String, String) -> SortedMap String (List String)
    addImporter acc (i, m) = insert i (m :: fromMaybe [] (lookup i acc)) acc

    -- each of our modules two or more of ours import, with its importers
    importedTwice : List (String, List String)
    importedTwice =
      let ours = the (SortedSet String) (fromList (map name fs))
          importersOf = foldl addImporter empty [ (show i.path, name f) | f <- fs, i <- f.mod.imports, contains (show i.path) ours ]
      in [ (m, sort (nub is)) | (m, is) <- SortedMap.toList importersOf, length (nub is) >= 2 ]

    ||| A module's group: its name without its last part.
    groupOf : String -> String
    groupOf m = case reverse (List1.forget (Data.String.split (== '.') m)) of
      (_ :: rest@(_ :: _)) => fastConcat (intersperse "." (reverse rest))
      _ => ""

    key : (String, List String) -> (String, List String)
    key (m, is) = (groupOf m, is)

    sameImporters : (String, List String) -> (String, List String) -> Bool
    sameImporters a b = key a == key b

    byGroupAndImporters : (String, List String) -> (String, List String) -> Ordering
    byGroupAndImporters a b = compare (key a) (key b)

    -- the siblings with the same importers, two or more of them
    twinClasses : List (String, List String) -> List (List String)
    twinClasses imported =
      filter (\c => length c >= 2) (map (map fst . List1.forget) (groupBy sameImporters (sortBy byGroupAndImporters (filter inGroup imported))))
      where
        inGroup : (String, List String) -> Bool
        inGroup (m, _) = groupOf m /= ""

    lastName : String -> String
    lastName m = maybe m id (last' (List1.forget (Data.String.split (== '.') m)))

    -- a set of siblings always imported together, and by whom
    together : List String -> String
    together c =
      let is = fromMaybe [] (head' c >>= \m => lookup m importedTwice) in
      listed (map lastName c) ++ " by " ++ show (length is) ++ " modules: " ++ listed (take 3 is) ++ (if length is > 3 then ", ..." else "")

    -- a group with members that could be joined: what share they are, and
    -- which, at four in five or more a candidate to collapse
    groupOffender : List String -> List (List String) -> String -> Maybe Offender
    groupOffender members classes g =
      let mine = filter (\c => maybe False (\m => groupOf m == g) (head' c)) classes
          size = length (filter (\m => groupOf m == g) members)
          joinable = length (joined mine)
          share = percent joinable size
      in if null mine then Nothing else
           Just (MkOffender g (minus joinable (length mine))
                   (show joinable ++ " of its " ++ show size ++ " members (" ++ show share ++ "%) could be joined without costing precision"
                    ++ (if share >= 80 then ", a candidate to collapse into one module" else "")
                    ++ ": " ++ fastConcat (intersperse "; " (map together mine))))
