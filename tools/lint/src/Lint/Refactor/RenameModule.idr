||| The refactoring `rename-module` (`renameModule`): a module given another
||| name, and its file another path to match.
|||
||| It is given the module's name and its new one, and acts on the module's
||| file. The file moves to the path of the new name, under the package's
||| `sourcedir`, its `module` line naming it; the package lists the new
||| name where it listed the old. Each importer imports the new name,
||| keeping its alias and whether the import is public. A name written
||| qualified by the old name, or by its last parts
||| (`IRCommon.Operators.Rel`), is written with as many last parts of the
||| new one (`IRCommon.Op.Rel`), all of them if it has fewer; a name written
||| under an alias stays, as the alias does. It renames nothing
||| when a module of the new name is among the files.
|||
||| What it leaves for after: the imports in order (`order-imports`), the
||| names qualified by the new paths (`qualify-names`), and the comments
||| that name the module, which only a person can tell from prose.
module Lint.Refactor.RenameModule

import Lint.Refactor.Change
import Lint.Refactor.Edit
import Lint.Refactor.Listing
import Lint.Refactor.Project
import Lint.Refactor.Refactoring
import Lint.Refactor.Span
import Lint.Refactor.Subject

import Core.FC
import Core.Name
import Core.Name.Namespace
import Data.List
import Data.List1
import Data.String
import Data.Zippable
import Idris.Syntax
import Lint.Rules
import Lint.Source

%default covering

||| `rename-module`: given a module's name and its new one, the module
||| renamed.
export
renameModule : (arguments : List String) -> Refactoring
renameModule args =
  MkRefactoring "rename-module" "rename a module (--arg OLD --arg NEW), its file moved and its importers rewritten"
    True False candidates
  where
    ||| A module's name.
    nameOf : Subject -> String
    nameOf s = show s.file.mod.moduleNS

    ||| The parts of a dotted name.
    partsOf : String -> List String
    partsOf m = forget (split (== '.') m)

    -- a name written qualified by the old module's last parts, written
    -- with as many of the new one's
    requalified : (old, new : String) -> (exports : List String) -> Subject -> (FC, Name) -> List Edit
    requalified old new exports t (fc, NS ns (UN (Basic n))) =
      let q = partsOf (show ns)
          k = length q
      in case bounds fc of
           Just ((l, c), (l', c')) =>
             let shown = substr (cast c) (cast (c' - c)) (lineOf t l) in
             if l /= l' || not (n `elem` exports) || not (isSuffixOf q (partsOf old)) || shown /= show ns ++ "." ++ n then []
             else [MkEdit (l, c) (l', c') (joinBy "." (drop (length (partsOf new) `minus` k) (partsOf new)) ++ "." ++ n)]
           Nothing => []
    requalified _ _ _ _ _ = []

    -- an importer's edits: its import of the old module made one of the
    -- new, with what follows the name kept, and the names written by the
    -- old module's name rewritten
    importerEdits : (old, new : String) -> (exports : List String) -> Subject -> Maybe (String, List Edit)
    importerEdits old new exports t =
      case List.filter (\i => show i.path == old) t.file.mod.imports of
        [] => Nothing
        is => Just (t.file.path, map importEdit is ++ concatMap (requalified old new exports t) t.written)
      where
        importEdit : Import -> Edit
        importEdit i =
          let at = fst (lineSpan i.loc)
              l = lineOf t at
              ws = words l
              after = drop 1 (dropWhile (/= old) ws)
              public' = if i.reexport then "public " else ""
          in MkEdit (at, 0) (at + 1, 0) (unwords (["import " ++ public' ++ new] ++ after) ++ "\n")

    -- the module renamed, or why not
    plan : Project -> Subject -> (old, new : String) -> Either String Change
    plan p s old new = do
      when (any (\t => nameOf t == new) p.files) $ Left ("`" ++ new ++ "` is among the files already")
      l <- listingOf p.packages old new
      ptext <- maybe (Left "the package's text cannot be read") Right (lookup l.package p.packages)
      let exports = nub (concatMap (.visible) s.declared)
          header = maybe (-1) fst (find (isPrefixOf "module " . snd) (zip [0 .. cast (length (linesOf s))] (linesOf s)))
          own = MkEdit (header, 0) (header + 1, 0) ("module " ++ new ++ "\n") :: concatMap (requalified old new exports s) s.written
          entry = l.indent ++ new ++ (if l.lastInList then "" else ",")
      when (header < 0) $ Left "it has no `module` line"
      text <- maybe (Left "its own edits overlap") Right (apply own s.text)
      pure (MkChange
              ((l.package, [replaceLines l.line l.line [entry]])
               :: mapMaybe (importerEdits old new exports) (List.filter (\t => nameOf t /= old) p.files))
              [(l.newPath, text)]
              [s.file.path])

    candidates : Project -> Subject -> List Candidate
    candidates p s = case args of
      [old, new] => if nameOf s == old then [MkCandidate ("rename " ++ old ++ " to " ++ new) (plan p s old new)] else []
      _ => []
