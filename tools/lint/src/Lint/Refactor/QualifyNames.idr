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
||| The names written bare are `Lint.Qualification`'s plan, which the rule
||| `unqualified` reports; the names written qualified otherwise, and the
||| imports' aliases, as `import-alias` checks them.
module Lint.Refactor.QualifyNames

import Lint.Refactor.Change
import Lint.Refactor.Edit
import Lint.Refactor.Project
import Lint.Refactor.Refactoring
import Lint.Refactor.Span
import Lint.Refactor.Subject

import Core.FC
import Core.Name
import Core.Name.Namespace
import Data.List
import Data.SortedMap
import Data.String
import Idris.Syntax
import Lint.Finding
import Lint.Qualification
import Lint.Qualifier
import Lint.Resolution
import Lint.Rules
import Lint.Source

%default covering

||| `qualify-names`: each name a file takes from another of our modules
||| written with where it comes from.
export
qualifyNames : Refactoring
qualifyNames =
  MkRefactoring "qualify-names"
    "write each name taken from another of our modules with its path past the common prefix"
    True False candidates
  where
    -- a name written qualified otherwise than the rule writes it, under
    -- an alias or a module's name (`LocatedIR.Load`), rewritten
    qualifiedEdits : Subject -> List Qualification.Imported -> (FC, Name) -> List Edit
    qualifiedEdits s is (fc, NS ns (UN (Basic n))) =
      let x = show ns
          names = \i => show i.imp.nameAs == x || i.name == x || isSuffixOf ("." ++ x) i.name
      in case (List.filter (\i => names i && (n `elem` i.exports)) is, Span.bounds fc) of
           ([i], Just ((l, c), (l', c'))) =>
             let shown = substr (cast c) (cast (c' - c)) (Subject.lineOf s l)
                 q = Qualifier.qualifiedName i.path n
             in if l /= l' || shown /= x ++ "." ++ n || shown == q then []
               else [MkEdit (l, c) (l', c') q]
           _ => []
    qualifiedEdits _ _ _ = []

    ||| The alias an import takes: the one its path asks, where the importer
    ||| writes the module's key type or the type's constructor.
    aliasFor : (uses : List (String, String)) -> Qualification.Imported -> Maybe String
    aliasFor uses i = case last' i.path of
      Just m => if any (\(d, n) => d == i.name && Qualifier.keyNamed m n) uses then Qualifier.aliasAt i.path
        else Nothing
      Nothing => Nothing

    -- an import whose alias is not the one the rule asks, rewritten
    importEdits : Subject -> List (String, String) -> Qualification.Imported -> List Edit
    importEdits s uses i =
      let want = aliasFor uses i
          have = if show i.imp.nameAs == i.name then Nothing else Just (show i.imp.nameAs)
          l = fst (Span.lineSpan i.imp.loc)
      in if want == have then [] else
           [MkEdit (l, 0) (l + 1, 0)
             ("import " ++ (if i.imp.reexport then "public " else "") ++ i.name
              ++ maybe "" (" as " ++) want ++ "\n")]

    ||| The imports of a file that are of our modules, with their paths: the
    ||| run's files' and the context's, the run's first.
    importedIn : Project -> Subject -> List Qualification.Imported
    importedIn p s =
      Qualification.importedFrom
        (fromList
          (reverse
            [ (show t.file.mod.moduleNS, nub (Finding.joined (map (.visible) t.declared)))
            | t <- p.files ++ p.context ]))
        s.file

    candidates : Project -> Subject -> List Refactoring.Candidate
    candidates p s = case Project.usesOf p (show s.file.mod.moduleNS) of
      Left why => [Refactoring.candidate "names" (Left why)]
      Right resolved =>
        let is = importedIn p s
            uses = [ (u.definer, u.name) | u <- resolved, not u.searched ]
            bare = Qualification.unqualified uses is s.file s.declared s.written
            requalified = Finding.joined (map (qualifiedEdits s is) s.written)
            imports = Finding.joined (map (importEdits s uses) is)
            named = nubBy (\a, b => a.from == b.from) (bare ++ requalified ++ imports)
            edits = named ++ Edit.realigned s.text named
        in if null edits then [] else [Refactoring.candidate "names" (Right (Change.inFile s.file.path edits))]
