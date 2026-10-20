||| Whether each of our modules is one piece (`separation`): a module whose
||| concepts fall apart into groups that no importer needs together is
||| several modules in one file.
|||
||| A module's concepts (`Lint.Concept`) cluster by use: two are of one
||| piece if some other module uses both. A module of several pieces could
||| be split along them at no importer's cost: none would import two
||| modules where it imported one, and each would import less of what it
||| does not use. That one piece refers to another is no reason to keep
||| them together: split, one module imports the other. But two that refer
||| to each other, through any of the module's concepts, are one piece:
||| split, each module would import the other, which Idris forbids; and so
||| are two that use one private helper, which a split would have to
||| export. Only
||| pieces some other module uses count: a piece no one imports is no
||| reason to split.
|||
||| Nor is a small one (`pieceLines`): a piece shorter than that would cost
||| more as a file than it saves its importers. A module counts the pieces
||| of that size it holds, one if it holds none. A module may leave itself
||| out with a reason (`-- lint: exclude separation: ...`), where a person
||| judges that its pieces belong together.
module Lint.Separation

import Lint.Concept
import Lint.Graph
import Lint.Precision
import Lint.Resolution
import Lint.Rules
import Lint.Source

import Data.List
import Data.Maybe
import Data.SortedMap
import Data.SortedSet

%default covering

||| A piece of a module: its concepts, and the other modules that use them.
record Piece where
  constructor MkPiece
  concepts : List String
  users : SortedSet String
  ||| The lines its concepts take.
  size : Nat

||| `separation`: of our modules some other module uses, how near each is
||| to one piece: the modules over the pieces they hold, 100 when every
||| module is one, each piece a group of concepts no importer needs with
||| another's. Its offenders, each module of several pieces, by the
||| pieces beyond the first, with what each holds and who uses it.
export
separation : List (Source.SourceFile, List Rules.Declared) -> Resolution -> Graph.Component
separation fds r =
  let byModule = Precision.conceptsByModule fds
      out = Precision.excludedFrom "separation" (map fst fds)
      counted =
        filter hasPieces
          [ (m, modulePieces byModule r.modules m) | m <- keys byModule, not (m `elem` out) ]
      pieces = sum (map (counting . snd) counted)
  in Graph.MkComponent "structure" "separation" (Graph.percent (length counted) pieces)
       ("modules that are one piece, of the pieces of " ++ show Concept.pieceLines
         ++ " lines or more their importers use: "
        ++ show (length counted) ++ " modules, " ++ show pieces ++ " pieces" ++ leftOut out)
       [ Graph.MkOffender m (minus (counting ps) 1)
         (show (counting ps) ++ " pieces: "
          ++ fastConcat (intersperse "; " (map described (filter large ps))))
       | (m, ps) <- counted, counting ps > 1 ]
  where
    hasPieces : (String, List Piece) -> Bool
    hasPieces (_, ps) = not (null ps)

    large : Piece -> Bool
    large p = p.size >= Concept.pieceLines

    -- the pieces of a module that count: those large enough, or one
    counting : List Piece -> Nat
    counting ps = max 1 (length (filter large ps))

    leftOut : List String -> String
    leftOut [] = ""
    leftOut ms = "; left out: " ++ Graph.listed ms

    described : Piece -> String
    described p =
      let us = Prelude.toList p.users in
      Graph.listed (take 4 p.concepts) ++ (if length p.concepts > 4 then ", ..." else "")
      ++ " (" ++ show p.size ++ " lines) used by " ++ Graph.listed (take 3 us)
        ++ (if length us > 3 then ", ..." else "")

    ||| A module's pieces: its concepts that other modules use, clustered by
    ||| use, each with its users.
    modulePieces : SortedMap String (List Concept) -> List Resolution.ResolvedModule -> String ->
                   List Piece
    modulePieces byModule rms m =
      let usersOf = usersMap (filter (.offered) (fromMaybe [] (lookup m byModule)))
      in map (piece usersOf)
        (parts (usedOnes usersOf)
         (sharing usersOf ++ cyclic (usedOnes usersOf) ++ sharingHelpers (usedOnes usersOf)))
      where
        concepts : List Concept
        concepts = fromMaybe [] (lookup m byModule)

        reaches : String -> SortedSet String
        reaches = Concept.reachable concepts

        -- two concepts that refer to each other, through any: one piece
        cyclic : List String -> List (String, String)
        cyclic ns =
          [ (a, b) | a <- ns, b <- ns, a < b, contains b (reaches a), contains a (reaches b) ]

        -- two concepts that reach one private concept, a helper both use:
        -- one piece, unless the helper were exported, which a split must
        -- not do
        sharingHelpers : List String -> List (String, String)
        sharingHelpers ns =
          let helpers = map (.name) (filter (not . (.offered)) concepts) in
          [ (a, b) | a <- ns, b <- ns, a < b,
            any (\h => contains h (reaches a) && contains h (reaches b)) helpers ]

        usedOnes : List (String, SortedSet String) -> List String
        usedOnes usersOf = [ n | (n, us) <- usersOf, not (null us) ]

        -- the other modules that use each concept
        usersMap : List Concept -> List (String, SortedSet String)
        usersMap cs =
          [ (c.name,
            fromList [ rm.name | rm <- rms,
                      rm.name /= m, contains c.name (Precision.usedConcepts byModule rm m) ])
           | c <- cs ]

        usersIn : List (String, SortedSet String) -> String -> SortedSet String
        usersIn usersOf n = fromMaybe empty (lookup n usersOf)

        -- two concepts some module uses both of
        sharing : List (String, SortedSet String) -> List (String, String)
        sharing usersOf =
          [ (a, b) | (a, ua) <- usersOf, (b, ub) <- usersOf, a < b,
           not (null (intersection ua ub)) ]

        piece : List (String, SortedSet String) -> List String -> Piece
        piece usersOf ns = MkPiece ns (foldr (\n, acc => union (usersIn usersOf n) acc) empty ns)
                                   (sum
                                     (map (.size)
                                       (filter (\c => c.name `elem` ns)
                                        (fromMaybe [] (lookup m byModule)))))

        ||| The connected parts of a graph, given its nodes and its edges, each part
        ||| its nodes in the order given.
        parts : List String -> List (String, String) -> List (List String)
        parts nodes edges = go nodes empty
          where
            neighbours : String -> List String
            neighbours n = [ b | (a, b) <- edges, a == n ] ++ [ a | (a, b) <- edges, b == n ]

            reach : SortedSet String -> List String -> SortedSet String
            reach seen [] = seen
            reach seen (n :: ns) = if contains n seen then reach seen ns
              else reach (insert n seen) (neighbours n ++ ns)

            go : List String -> SortedSet String -> List (List String)
            go [] _ = []
            go (n :: ns) done =
              if contains n done then go ns done
              else let part = reach empty [n] in filter (`contains` part) nodes
                :: go ns (union done part)
