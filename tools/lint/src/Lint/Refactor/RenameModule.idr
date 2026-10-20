||| The refactoring `rename-module` (`renameModule`): a module given another
||| name, and its file another path to match.
|||
||| It is given the module's name and its new one, and acts on the module's
||| file; or a group's and its new one, and renames each module of the
||| group to the same place under the new (`Compiler.Native.TermIR.Instr`
||| to `Native.Codegen.TermIR.Instr`), one at a time. The file moves to the
||| path of the new name, under the package's `sourcedir`, its `module` line
||| naming it; the package lists the new name where it listed the old, or,
||| if its list is in order, where the order puts it. Each importer imports
||| the new name, keeping its alias and whether the import is public. A
||| name written qualified by the old name, or by its last parts
||| (`IRCommon.Operators.Rel`), is written with as many last parts of the
||| new one (`IRCommon.Op.Rel`), all of them if it has fewer; a name written
||| under an alias stays, as the alias does. It renames nothing when a
||| module of the new name is among the files.
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
  MkRefactoring "rename-module"
    "rename a module or a group (--arg OLD --arg NEW), its files moved and its importers rewritten"
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
    requalified : (old, new : String) -> (exports : List String) -> Subject -> (FC, Name) ->
                  List Edit
    requalified old new exports t (fc, NS ns (UN (Basic n))) =
      let q = partsOf (show ns)
          k = length q
      in case Span.bounds fc of
           Just ((l, c), (l', c')) =>
             let shown = substr (cast c) (cast (c' - c)) (Subject.lineOf t l) in
             if l /= l' || not (n `elem` exports) || not (isSuffixOf q (partsOf old)) || shown
               /= show ns ++ "." ++ n then []
             else
               [MkEdit (l, c) (l', c')
                (joinBy "." (drop (length (partsOf new) `minus` k) (partsOf new)) ++ "." ++ n)]
           Nothing => []
    requalified _ _ _ _ _ = []

    -- an importer's edits: its import of the old module made one of the
    -- new, with what follows the name kept, and the names written by the
    -- old module's name rewritten
    importerEdits : (old, new : String) -> (exports : List String) -> Subject ->
                    Maybe (String, List Edit)
    importerEdits old new exports t =
      case List.filter (\i => show i.path == old) t.file.mod.imports of
        [] => Nothing
        is =>
          Just (t.file.path,
                map importEdit is ++ concatMap (requalified old new exports t) t.written)
      where
        importEdit : Import -> Edit
        importEdit i =
          let at = fst (Span.lineSpan i.loc)
              l = Subject.lineOf t at
              ws = words l
              after = drop 1 (dropWhile (/= old) ws)
              public' = if i.reexport then "public " else ""
          in MkEdit (at, 0) (at + 1, 0) (unwords (["import " ++ public' ++ new] ++ after) ++ "\n")

    -- the module renamed, or why not
    plan : Project -> Subject -> (old, new : String) -> Either String Change
    plan p s old new = do
      when (any (\t => nameOf t == new) p.files) $
        Left ("`" ++ new ++ "` is among the files already")
      l <- Listing.listingOf p.packages old new
      ptext <- maybe (Left "the package's text cannot be read") Right (lookup l.package p.packages)
      let exports = nub (concatMap (.visible) s.declared)
          header =
            maybe (-1) fst
              (find (isPrefixOf "module " . snd) (zip [0 .. cast (length (Subject.linesOf s))] (Subject.linesOf s)))
          own = MkEdit (header, 0) (header + 1, 0) ("module " ++ new ++ "\n")
            :: concatMap (requalified old new exports s) s.written
          entry = l.indent ++ new ++ (if l.lastInList then "" else ",")
          -- a list in order stays in order, the new name in its place
          listed = case Listing.moduleList ptext of
            Just ml => if sort ml.modules == ml.modules
                         then Edit.replaceLines ml.first ml.last
                           (Listing.moduleLines ml.indent
                            (sort (map (\m => if m == old then new else m) ml.modules)))
                         else Edit.replaceLines l.line l.line [entry]
            Nothing => Edit.replaceLines l.line l.line [entry]
      when (header < 0) $ Left "it has no `module` line"
      text <- maybe (Left "its own edits overlap") Right (Edit.apply own s.text)
      pure (MkChange
              ((l.package, [listed])
               :: mapMaybe (importerEdits old new exports)
                 (List.filter (\t => nameOf t /= old) p.files))
              [(l.newPath, text)]
              [s.file.path])

    -- a module's new name: the new one for the old, and for a module of
    -- the old group the same place under the new
    renamed : (old, new, module' : String) -> Maybe String
    renamed old new m =
      if m == old then Just new
      else if isPrefixOf (old ++ ".") m then Just (new ++ substr (length old) (length m) m)
      else Nothing

    candidates : Project -> Subject -> List Refactoring.Candidate
    candidates p s = case args of
      [old, new] => case renamed old new (nameOf s) of
        Just m => [Refactoring.candidate ("rename " ++ nameOf s ++ " to " ++ m) (plan p s (nameOf s) m)]
        Nothing => []
      _ => []
