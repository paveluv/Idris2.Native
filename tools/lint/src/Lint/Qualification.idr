||| Where a module of ours writes bare a name another of ours defines, the
||| name as `Lint.Qualifier` writes it (`unqualified`): one plan, which the
||| refactoring `qualify-names` makes and the rule `unqualified` reports.
|||
||| Left as they are: names of the libraries' modules (the Prelude's, the
||| Idris API's), names the file defines (its constructors, fields and
||| methods among them, which may share a name with another's type), local
||| variables, operators and projections, which cannot be qualified, and a
||| name the module takes from two modules, resolved from its TTC, as
||| `length` might be the Prelude's and ours: which occurrence means which,
||| only the type checker knew.
module Lint.Qualification

import Lint.Concept
import Lint.Finding
import Lint.Qualifier
import Lint.Refactor.Edit as Refactor
import Lint.Refactor.Free
import Lint.Refactor.Span
import Lint.Rules
import Lint.Source

import Core.FC
import Core.Name
import Core.Name.Namespace
import Data.List
import Data.Maybe
import Data.SortedMap
import Idris.Syntax
import Libraries.Data.WithData

%default covering

||| One of our modules a file imports: its name, its path past what it
||| shares with the importer's (`TermIR.StaticDef` from
||| `Native.Codegen.RegAlloc`), the import, and the names it exports.
public export
record Imported where
  constructor MkImported
  name : String
  path : List String
  imp : Import
  exports : List String

||| The imports of a file that are of our modules, by the names each of our
||| modules exports, with their paths.
export
importedFrom : (exportsOf : SortedMap String (List String)) -> Source.SourceFile -> List Imported
importedFrom exportsOf f = mapMaybe imported f.mod.imports
  where
    imported : Import -> Maybe Imported
    imported i =
      map (MkImported (show i.path) (Qualifier.pathFrom (show f.mod.moduleNS) (show i.path)) i)
        (lookup (show i.path) exportsOf)

||| Each name the file writes bare that it takes from one of our modules
||| alone, by what it uses resolved (`uses`, each with its definer), and
||| that the rule writes qualified: an edit to the qualified name, where it
||| is written.
export
unqualified : (uses : List (String, String)) -> List Imported -> Source.SourceFile ->
              List Rules.Declared ->
              (written : List (FC, Name)) -> List Refactor.Edit
unqualified uses is f ds written =
  let defined = Finding.joined (map (.defines) ds)
        ++ Finding.joined (map (.members) (Concept.conceptsOf f ds))
      lower = [ o | d <- ds, o <- SortedMap.toList (freeIn d), not (capital (fst o)) ]
  in Finding.joined (map (bareEdits defined) (lower ++ SortedMap.toList capitals))
  where
    capital : String -> Bool
    capital n = maybe False isUpper (head' (unpack n))

    ||| The free names of a declaration, each where it is written: a claim's,
    ||| a definition's, a `mutual` block's, followed by Free; an
    ||| implementation's and an interface's by their members'; a data type's
    ||| or a record's none, its names all capitalised ones (`capitals`).
    freeIn : Rules.Declared -> Refactor.Free.Occurrences
    freeIn d = case d.decl.val of
      PImplementation _ _ _ _ _ _ _ _ _ (Just body) =>
        Refactor.Free.allOf (map Refactor.Free.declAt body)
      PInterface _ _ _ _ _ _ _ body => Refactor.Free.allOf (map Refactor.Free.declAt body)
      PData {} => empty
      PRecord {} => empty
      _ => Refactor.Free.declAt d.decl

    ||| Each capitalised name the file writes bare, wherever it is: a type or
    ||| a constructor, in an expression or a pattern, never a variable,
    ||| where the free names have none in a clause's patterns.
    capitals : Refactor.Free.Occurrences
    capitals = foldr (\(fc, n), acc => case (n, Refactor.Span.bounds fc) of
                                         (UN (Basic x), Just (start, _)) =>
                                           if capital x
                                             then insert x (start :: fromMaybe [] (lookup x acc))
                                               acc else acc
                                         _ => acc) empty written

    -- the one import of ours that exports a name, if exactly one does,
    -- and the module takes the name from it alone, resolved: not from a
    -- library too
    providerOf : String -> Maybe Imported
    providerOf n = case List.filter (\i => n `elem` i.exports) is of
      [i] => if map fst (List.filter (\u => snd u == n) uses) == [i.name] then Just i else Nothing
      _ => Nothing

    -- a name written bare, made qualified
    bareEdits : (defined : List String) -> (String, List (Int, Int)) -> List Refactor.Edit
    bareEdits defined (n, ps) =
      if n `elem` defined then [] else
        case providerOf n of
          Just i => let q = Qualifier.qualifiedName i.path n in
                    if q == n then []
                      else [ Refactor.MkEdit p (fst p, snd p + cast (length n)) q | p <- ps,
                            p /= (-1, -1) ]
          Nothing => []
