||| The refactoring `join-modules` (`joinModules`): modules joined into one,
||| the inverse of `split-module`, for a group split further than its
||| concepts are apart.
|||
||| It is given the module to make and the modules to join, and acts on the
||| file of the first of them. The new file takes their declarations as
||| written, with what is attached above them, in the order the modules are
||| given; their imports, but of each other; and the first one's
||| `%default`. Each importer imports the new module where it imported the
||| first of the joined ones, keeping its alias, and no longer the others;
||| the package lists the new module where it listed the first, and none of
||| the others; their files go. It joins nothing when two of the modules
||| define one name, or when one imports a module that imports another of
||| them, which would then import the new one that imports it.
|||
||| What it leaves for after: the imports in order (`order-imports`), those
||| a module no longer needs (`prune-imports`), and the new module's
||| documentation, which only a person can write: the joined modules' own
||| go with their files.
module Lint.Refactor.JoinModules

import Lint.Refactor.Change
import Lint.Refactor.Edit
import Lint.Refactor.Extent
import Lint.Refactor.Listing
import Lint.Refactor.Project
import Lint.Refactor.Refactoring
import Lint.Refactor.Span
import Lint.Refactor.Subject

import Core.Name.Namespace
import Core.WithData
import Data.List
import Data.Maybe
import Data.String
import Data.Zippable
import Idris.Syntax
import Libraries.Data.WithData
import Lint.Finding
import Lint.Rules
import Lint.Source

%default covering

||| `join-modules`: given the module to make and the modules to join, them
||| joined.
export
joinModules : (arguments : List String) -> Refactoring
joinModules args =
  MkRefactoring "join-modules" "join modules into one (--arg NEW --arg MODULE...), their importers rewritten"
    True False candidates
  where
    -- the alias an import gives its module, if any
    aliasOf : (Import, String) -> Maybe String
    aliasOf (_, l) = case break (== "as") (words l) of
      (_, "as" :: a :: _) => Just a
      _ => Nothing

    ||| The imports of a module as written, a line each.
    importLines : Subject -> List (Import, String)
    importLines s = map (\i => (i, trim (lineOf s (fst (lineSpan i.loc))))) s.file.mod.imports

    -- an importer's edits: the first import of the joined modules made one
    -- of the new module, keeping an alias any of them gives and whether one
    -- is public, and the others taken out; an alias that is the new
    -- module's own last name goes, as the name qualifies by itself
    importerEdits : (into : String) -> (sources : List String) -> Subject -> Maybe (String, List Edit)
    importerEdits into sources t =
      case List.filter (\(i, _) => show i.path `elem` sources) (importLines t) of
        [] => Nothing
        ((i, l) :: rest) =>
          let alias = case List.filter (/= lastPart into) (mapMaybe aliasOf ((i, l) :: rest)) of
                        (a :: _) => " as " ++ a
                        [] => ""
              public' = if any (\(j, _) => j.reexport) ((i, l) :: rest) then "public " else ""
              at = fst (lineSpan i.loc)
          in Just (t.file.path, MkEdit (at, 0) (at + 1, 0) ("import " ++ public' ++ into ++ alias ++ "\n")
                                :: map (\(j, _) => deleteLines (fst (lineSpan j.loc)) (fst (lineSpan j.loc))) rest)

    ||| A module's declarations as written: from what is attached above its
    ||| first to its end, the trailing blank lines aside. Its `%default` is no
    ||| declaration of it here: the new module has one.
    bodyOf : Subject -> List String
    bodyOf s = case sort (map (fst . lineSpan . (.decl.fc)) (List.filter (not . defaultDirective) s.declared)) of
      (first :: _) => reverse (dropWhile (\l => trim l == "") (reverse (drop (cast (attachedFrom (linesOf s) first)) (linesOf s))))
      [] => []
      where
        ||| Whether a declaration is a `%default` directive.
        defaultDirective : Declared -> Bool
        defaultDirective d = case d.decl.val of
          PDirective (DefaultTotality _) => True
          _ => False

    -- the new module's text: a placeholder for its documentation, the
    -- joined modules' imports but of each other, the first one's
    -- `%default`, and their declarations
    newText : (into : String) -> (sources : List String) -> List Subject -> String
    newText into sources ss =
      let imports = sort (nub [ l | s <- ss, (i, l) <- importLines s, not (show i.path `elem` sources) ])
          (publics, privates) = partition (isPrefixOf "import public") imports
          defaults = take 1 [ trim l | s <- take 1 ss, l <- linesOf s, isPrefixOf "%default" (trim l) ]
      in unlines (["||| " ++ joinBy ", " (map (\m => "`" ++ lastPart m ++ "`") sources) ++ ", joined.", "module " ++ into, ""]
                  ++ block publics ++ block privates ++ block defaults
                  ++ joined (intersperse [""] (map bodyOf ss)))
      where
        block : List String -> List String
        block [] = []
        block ls = ls ++ [""]

    -- the names a list holds more than once
    twice : List String -> List String
    twice ns = nub [ n | (n, k) <- zip ns [0 .. length ns], n `elem` take k ns ]

    ||| A module's name.
    nameOf : Subject -> String
    nameOf s = show s.file.mod.moduleNS

    -- the modules joined, or why not
    plan : Project -> (into : String) -> (sources : List String) -> Either String Change
    plan p into sources = do
      ss <- traverse (\m => maybe (Left ("`" ++ m ++ "` is not among the files")) Right (find (\s => nameOf s == m) p.files)) sources
      let names = joined (map (\s => nub (joined (map (.defines) s.declared))) ss)
      case twice names of
        [] => pure ()
        ns => Left ("two of the modules define " ++ joinBy ", " (map (\n => "`" ++ n ++ "`") ns))
      let outside = nub [ show i.path | s <- ss, i <- s.file.mod.imports, not (show i.path `elem` sources) ]
          around = List.filter (\t => (nameOf t `elem` outside) && any (\i => show i.path `elem` sources) t.file.mod.imports) p.files
      when (not (null around)) $
        Left ("`" ++ joinBy "`, `" (map nameOf around) ++ "` imports one of the modules and is imported by another: the new one would import itself")
      l <- listingOf p.packages (fromMaybe "" (head' sources)) into
      ml <- maybe (Left "the package's list of modules cannot be read") Right
                  (lookup l.package p.packages >>= moduleList)
      let kept = mapMaybe (\m => if m `elem` sources then (if Just m == head' sources then Just into else Nothing) else Just m) ml.modules
      pure (MkChange
              ((l.package, [replaceLines ml.first ml.last (moduleLines ml.indent kept)])
               :: mapMaybe (importerEdits into sources) (List.filter (\t => not (nameOf t `elem` sources)) p.files))
              [(l.newPath, newText into sources ss)]
              (map (.file.path) ss))

    candidates : Project -> Subject -> List Candidate
    candidates p s = case args of
      (into :: sources@(first :: _ :: _)) =>
        if nameOf s == first then [MkCandidate ("join " ++ joinBy ", " sources ++ " into " ++ into) (plan p into sources)] else []
      _ => []
