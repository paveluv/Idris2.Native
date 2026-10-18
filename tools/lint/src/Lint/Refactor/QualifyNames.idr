||| The refactoring `qualify-names` (`qualifyNames`), an experiment: each
||| name a module takes from another of ours written with where it comes
||| from, the same way everywhere in the module, so that a reader without an
||| editor sees it.
|||
||| A name `A` from our module `M`, used in the module `C`, is written with
||| `M`'s path past what it shares with `C`'s: in `Native.Codegen.RegAlloc`,
||| `SWord` of `Native.Codegen.TermIR.StaticDef` is
||| `TermIR.StaticDef.SWord`, and `piece` of `Data.Builder`
||| `Data.Builder.piece`. A type named after its module drops the module's
||| last part, `TermIR.StaticDef`, which Idris resolves through an alias,
||| so the module is imported under the rest of the path
||| (`import Native.Codegen.TermIR.StaticDef as TermIR`); a peer's, of the
||| same group, stays bare (`Target`). Every name thus has one
||| qualifier in a module, and no two of ours meet bare.
|||
||| Left as they are: names of the libraries' modules (the Prelude's, the
||| Idris API's), names the file defines (its constructors, fields and
||| methods among them, which may share a name with another's type), local
||| variables, operators and
||| projections, which cannot be qualified, and a name the module takes from
||| two modules, resolved from its TTC, as `length` might be the Prelude's
||| and ours: which occurrence means which, only the type checker knew.
module Lint.Refactor.QualifyNames

import Lint.Refactor.Change
import Lint.Refactor.Edit
import Lint.Refactor.Free
import Lint.Refactor.Project
import Lint.Refactor.Refactoring
import Lint.Refactor.Span
import Lint.Refactor.Subject

import Core.FC
import Core.Name
import Core.Name.Namespace
import Core.WithData
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.String
import Idris.Syntax
import Libraries.Data.WithData
import Lint.Concept
import Lint.Finding
import Lint.Qualifier
import Lint.Resolution
import Lint.Rules
import Lint.Source

%default covering

||| One of our modules a file imports: its name, its path past what it
||| shares with the importer's (`TermIR.StaticDef` from
||| `Native.Codegen.RegAlloc`), the import, and the names it exports.
record Imported where
  constructor MkImported
  name : String
  path : List String
  imp : Import
  exports : List String

||| `qualify-names`: each name a file takes from another of our modules
||| written with where it comes from.
export
qualifyNames : Refactoring
qualifyNames =
  MkRefactoring "qualify-names" "write each name taken from another of our modules with its path past the common prefix (an experiment)"
    True False candidates
  where
    -- the one import of ours that exports a name, if exactly one does,
    -- and the module takes the name from it alone, resolved: not from a
    -- library too
    providerOf : List (String, String) -> List Imported -> String -> Maybe Imported
    providerOf uses is n = case List.filter (\i => n `elem` i.exports) is of
      [i] => if map fst (List.filter (\u => snd u == n) uses) == [i.name] then Just i else Nothing
      _ => Nothing

    ||| A name of an imported module as the importer writes it.
    qualified : Imported -> String -> String
    qualified i = qualifiedName i.path

    -- a name written bare, made qualified
    bareEdits : List (String, String) -> List Imported -> (defined : List String) -> (String, List (Int, Int)) -> List Edit
    bareEdits uses is defined (n, ps) =
      if n `elem` defined then [] else
        case providerOf uses is n of
          Just i => let q = qualified i n in
                    if q == n then [] else [ MkEdit p (fst p, snd p + cast (length n)) q | p <- ps, p /= (-1, -1) ]
          Nothing => []

    -- a name written qualified otherwise than the rule writes it, under
    -- an alias or a module's name (`LocatedIR.Load`), rewritten
    qualifiedEdits : Subject -> List Imported -> (FC, Name) -> List Edit
    qualifiedEdits s is (fc, NS ns (UN (Basic n))) =
      let x = show ns
          names = \i => show i.imp.nameAs == x || i.name == x || isSuffixOf ("." ++ x) i.name
      in case (List.filter (\i => names i && (n `elem` i.exports)) is, bounds fc) of
           ([i], Just ((l, c), (l', c'))) =>
             let shown = substr (cast c) (cast (c' - c)) (lineOf s l)
                 q = qualified i n
             in if l /= l' || shown /= x ++ "." ++ n || shown == q then [] else [MkEdit (l, c) (l', c') q]
           _ => []
    qualifiedEdits _ _ _ = []

    ||| The alias an import takes: the one its path asks, where the importer
    ||| writes the module's key type or the type's constructor.
    aliasFor : (uses : List (String, String)) -> Imported -> Maybe String
    aliasFor uses i = case last' i.path of
      Just m => if any (\(d, n) => d == i.name && keyNamed m n) uses then aliasAt i.path else Nothing
      Nothing => Nothing

    -- an import whose alias is not the one the rule asks, rewritten
    importEdits : Subject -> List (String, String) -> Imported -> List Edit
    importEdits s uses i =
      let want = aliasFor uses i
          have = if show i.imp.nameAs == i.name then Nothing else Just (show i.imp.nameAs)
          l = fst (lineSpan i.imp.loc)
      in if want == have then [] else
           [MkEdit (l, 0) (l + 1, 0) ("import " ++ (if i.imp.reexport then "public " else "") ++ i.name ++ maybe "" (" as " ++) want ++ "\n")]

    ||| The imports of a file that are of our modules, with their paths.
    importedIn : Project -> Subject -> List Imported
    importedIn p s = mapMaybe imported s.file.mod.imports
      where
        imported : Import -> Maybe Imported
        imported i =
          map (\t => MkImported (show i.path) (pathFrom (show s.file.mod.moduleNS) (show i.path)) i (nub (joined (map (.visible) t.declared))))
              (find (\t => show t.file.mod.moduleNS == show i.path) (p.files ++ p.context))
    ||| The free names of a declaration, each where it is written: a claim's,
    ||| a definition's, a `mutual` block's, followed by Free; an
    ||| implementation's and an interface's by their members'; a data type's
    ||| or a record's none, its names all capitalised ones (`capitals`).
    freeIn : Declared -> Occurrences
    freeIn d = case d.decl.val of
      PImplementation _ _ _ _ _ _ _ _ _ (Just body) => allOf (map declAt body)
      PInterface _ _ _ _ _ _ _ body => allOf (map declAt body)
      PData {} => empty
      PRecord {} => empty
      _ => declAt d.decl

    capital : String -> Bool
    capital n = maybe False isUpper (head' (unpack n))

    ||| Each capitalised name the file writes bare, wherever it is: a type or
    ||| a constructor, in an expression or a pattern, never a variable,
    ||| where the free names have none in a clause's patterns.
    capitals : Subject -> Occurrences
    capitals s = foldr (\(fc, n), acc => case (n, bounds fc) of
                                           (UN (Basic x), Just (start, _)) =>
                                             if capital x then insert x (start :: fromMaybe [] (lookup x acc)) acc else acc
                                           _ => acc) empty s.written

    candidates : Project -> Subject -> List Candidate
    candidates p s = case p.resolution of
      Nothing => [candidate "names" (Left "the modules' uses cannot be resolved: build them first")]
      Just r =>
        let is = importedIn p s
            uses = [ (u.definer, u.name) | rm <- r.modules, rm.name == show s.file.mod.moduleNS, u <- rm.uses, not u.searched ]
            defined = joined (map (.defines) s.declared) ++ joined (map (.members) (conceptsOf s.file s.declared))
            lower = [ o | d <- s.declared, o <- SortedMap.toList (freeIn d), not (capital (fst o)) ]
            bare = joined (map (bareEdits uses is defined) (lower ++ SortedMap.toList (capitals s)))
            requalified = joined (map (qualifiedEdits s is) s.written)
            imports = joined (map (importEdits s uses) is)
            named = nubBy (\a, b => a.from == b.from) (bare ++ requalified ++ imports)
            edits = named ++ realigned s.text named
        in if null edits then [] else [candidate "names" (Right (inFile s.file.path edits))]
