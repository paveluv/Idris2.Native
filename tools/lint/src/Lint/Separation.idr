||| Whether each of our modules is one piece (`separation`): a module whose
||| concepts fall apart into groups that no importer needs together is
||| several modules in one file.
|||
||| A module's concepts (`Lint.Concept`) cluster by use: two are of one
||| piece if some other module uses both. A module of several pieces could
||| be split along them at no importer's cost: none would import two
||| modules where it imported one, and each would import less of what it
||| does not use. That the pieces refer to each other is no reason to keep
||| them together: split, one module imports the other. Only pieces some
||| other module uses count: a piece no one imports is no reason to split.
module Lint.Separation

import Data.List
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Lint.Concept
import Lint.Graph
import Lint.Precision
import Lint.Resolution
import Lint.Rules
import Lint.Source

%default covering

||| A piece of a module: its concepts, and the other modules that use them.
record Piece where
  constructor MkPiece
  concepts : List String
  users : SortedSet String

||| `separation`: of our modules some other module uses, how near each is
||| to one piece: the modules over the pieces they hold, 100 when every
||| module is one, each piece a group of concepts no importer needs with
||| another's. Its offenders, each module of several pieces, by the
||| pieces beyond the first, with what each holds and who uses it.
export
separation : List (SourceFile, List Declared) -> Resolution -> Component
separation fds r =
  let byModule = conceptsByModule fds
      counted = filter hasPieces [ (m, piecesOf byModule r.modules m) | m <- keys byModule ]
      pieces = sum (map (length . snd) counted)
  in MkComponent "structure" "separation" (percent (length counted) pieces)
       ("modules that are one piece, of the pieces their importers use: " ++ show (length counted) ++ " modules, " ++ show pieces ++ " pieces")
       [ MkOffender m (minus (length ps) 1) (show (length ps) ++ " pieces: " ++ fastConcat (intersperse "; " (map described ps)))
       | (m, ps) <- counted, length ps > 1 ]
  where
    hasPieces : (String, List Piece) -> Bool
    hasPieces (_, ps) = not (null ps)

    described : Piece -> String
    described p =
      let us = Prelude.toList p.users in
      listed (take 4 p.concepts) ++ (if length p.concepts > 4 then ", ..." else "")
      ++ " used by " ++ listed (take 3 us) ++ (if length us > 3 then ", ..." else "")

    ||| A module's pieces: its concepts that other modules use, clustered by
    ||| use, each with its users.
    piecesOf : SortedMap String (List Concept) -> List ResolvedModule -> String -> List Piece
    piecesOf byModule rms m =
      let usersOf = usersMap (filter (.offered) (fromMaybe [] (lookup m byModule)))
      in map (piece usersOf) (parts (usedOnes usersOf) (sharing usersOf))
      where
        usedOnes : List (String, SortedSet String) -> List String
        usedOnes usersOf = [ n | (n, us) <- usersOf, not (null us) ]

        -- the other modules that use each concept
        usersMap : List Concept -> List (String, SortedSet String)
        usersMap cs = [ (c.name, fromList [ rm.name | rm <- rms, rm.name /= m, contains c.name (usedOf byModule rm m) ]) | c <- cs ]

        usersIn : List (String, SortedSet String) -> String -> SortedSet String
        usersIn usersOf n = fromMaybe empty (lookup n usersOf)

        -- two concepts some module uses both of
        sharing : List (String, SortedSet String) -> List (String, String)
        sharing usersOf = [ (a, b) | (a, ua) <- usersOf, (b, ub) <- usersOf, a < b, not (null (intersection ua ub)) ]

        piece : List (String, SortedSet String) -> List String -> Piece
        piece usersOf ns = MkPiece ns (foldr (\n, acc => union (usersIn usersOf n) acc) empty ns)

        ||| The connected parts of a graph, given its nodes and its edges, each part
        ||| its nodes in the order given.
        parts : List String -> List (String, String) -> List (List String)
        parts nodes edges = go nodes empty
          where
            neighbours : String -> List String
            neighbours n = [ b | (a, b) <- edges, a == n ] ++ [ a | (a, b) <- edges, b == n ]

            reach : SortedSet String -> List String -> SortedSet String
            reach seen [] = seen
            reach seen (n :: ns) = if contains n seen then reach seen ns else reach (insert n seen) (neighbours n ++ ns)

            go : List String -> SortedSet String -> List (List String)
            go [] _ = []
            go (n :: ns) done =
              if contains n done then go ns done
              else let part = reach empty [n] in filter (`contains` part) nodes :: go ns (union done part)
