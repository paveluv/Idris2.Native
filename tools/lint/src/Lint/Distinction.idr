||| How far each group of modules is split apart (`distinction`): siblings
||| that the same modules always import together could be one module, and
||| a group most of whose members could be joined so is oversplit.
|||
||| A group is the modules under one parent (`Native.Codegen.TermIR`'s
||| `Opnd`, `Instr`, ...); modules at the top are in none, and a module
||| alone under its parent has no sibling to join. Two
||| members with the same importers, at least two, are imported together
||| every time: no importer takes one without the other, so joining them
||| would cost none of them precision. One importer is no evidence: a module
||| imported once is imported with whatever else its importer needs. A
||| member too small to stand alone, its concepts shorter than a piece is
||| worth (`pieceLines`), could be joined to a sibling too: the rule that
||| keeps a small piece in its module, read backwards. A group's share of
||| members that could be joined says how oversplit it is; at four in five
||| or more, the group is a candidate to collapse into one module.
module Lint.Distinction

import Lint.Concept
import Lint.Finding
import Lint.Graph
import Lint.Rules
import Lint.Source

import Core.Name.Namespace
import Data.List
import Data.List1
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Data.String
import Idris.Syntax

%default covering

||| `distinction`: of the members of our groups, the share imported apart
||| from every sibling. Its offenders, each group with members that could
||| be joined, by the modules joining would remove: what share of the group
||| that is, and which siblings are always imported together, by whom.
export
distinction : List (Source.SourceFile, List Rules.Declared) -> Graph.Component
distinction fds =
  let grouped = filter (\m => moduleGroup m /= "") (map name fs)
      members =
        filter (\m => length (filter (\o => moduleGroup o == moduleGroup m) grouped) >= 2) grouped
      classes = twinClasses importedTwice
      small = filter (\(m, _) => m `elem` members) smallMembers
      joinable = length (nub (Finding.joined classes ++ map fst small))
  in Graph.MkComponent "structure" "distinction"
    (Graph.percent (minus (length members) joinable) (length members))
       ("group members that stand apart from their siblings: "
         ++ show (minus (length members) joinable) ++ " of " ++ show (length members))
       (mapMaybe (groupOffender members classes small) (nub (map moduleGroup members)))
  where
    fs : List Source.SourceFile
    fs = map fst fds

    name : Source.SourceFile -> String
    name f = show f.mod.moduleNS


    addImporter : SortedMap String (List String) -> (String, String) ->
                  SortedMap String (List String)
    addImporter acc (i, m) = insert i (m :: fromMaybe [] (lookup i acc)) acc

    -- each of our modules two or more of ours import, with its importers
    importedTwice : List (String, List String)
    importedTwice =
      let ours = the (SortedSet String) (fromList (map name fs))
          importersOf =
            foldl addImporter empty
              [ (show i.path, name f) | f <- fs, i <- f.mod.imports, contains (show i.path) ours ]
      in [ (m, sort (nub is)) | (m, is) <- SortedMap.toList importersOf, length (nub is) >= 2 ]

    ||| A module's group: its name without its last part.
    moduleGroup : String -> String
    moduleGroup m = case reverse (List1.forget (Data.String.split (== '.') m)) of
      (_ :: rest@(_ :: _)) => fastConcat (intersperse "." (reverse rest))
      _ => ""

    -- the members of groups too small to stand alone, with their sizes
    smallMembers : List (String, Nat)
    smallMembers =
      [ (name f, size) | (f, ds) <- fds, moduleGroup (name f) /= "",
        let size = sum (map (.size) (Concept.fileConcepts f ds)), size < Concept.pieceLines ]

    key : (String, List String) -> (String, List String)
    key (m, is) = (moduleGroup m, is)

    sameImporters : (String, List String) -> (String, List String) -> Bool
    sameImporters a b = key a == key b

    byGroupAndImporters : (String, List String) -> (String, List String) -> Ordering
    byGroupAndImporters a b = compare (key a) (key b)

    -- the siblings with the same importers, two or more of them
    twinClasses : List (String, List String) -> List (List String)
    twinClasses imported =
      filter (\c => length c >= 2)
        (map (map fst . List1.forget)
         (groupBy sameImporters (sortBy byGroupAndImporters (filter inGroup imported))))
      where
        inGroup : (String, List String) -> Bool
        inGroup (m, _) = moduleGroup m /= ""

    lastName : String -> String
    lastName m = maybe m id (last' (List1.forget (Data.String.split (== '.') m)))

    -- a set of siblings always imported together, and by whom
    together : List String -> String
    together c =
      let is = fromMaybe [] (head' c >>= \m => lookup m importedTwice) in
      Graph.listed (map lastName c) ++ " by " ++ show (length is) ++ " modules: "
        ++ Graph.listed (take 3 is)
        ++ (if length is > 3 then ", ..." else "")

    -- a group with members that could be joined: what share they are, and
    -- which, at four in five or more a candidate to collapse
    groupOffender : List String -> List (List String) -> List (String, Nat) -> String ->
                    Maybe Graph.Offender
    groupOffender members classes small g =
      let mine = filter (\c => maybe False (\m => moduleGroup m == g) (head' c)) classes
          tiny = filter (\(m, _) => moduleGroup m == g) small
          size = length (filter (\m => moduleGroup m == g) members)
          joinable = nub (Finding.joined mine ++ map fst tiny)
          share = Graph.percent (length joinable) size
      in if null joinable || size < 2 then Nothing else
           Just (Graph.MkOffender g (minus (length joinable) (length mine))
                   (show (length joinable) ++ " of its " ++ show size ++ " members (" ++ show share
                     ++ "%) could be joined"
                    ++ (if share >= 80 then ", a candidate to collapse into one module" else "")
                    ++ ": " ++ fastConcat (intersperse "; " (map together mine ++ smallOnes tiny))))
      where
        smallOnes : List (String, Nat) -> List String
        smallOnes [] = []
        smallOnes ts =
          ["too small to stand alone: "
           ++ joinBy ", " (map (\(m, n) => "`" ++ lastName m ++ "` (" ++ show n ++ " lines)") ts)]
