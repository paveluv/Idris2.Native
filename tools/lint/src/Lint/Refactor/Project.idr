||| What a wide refactoring sees beside the file it looks at (`Project`):
||| every file of the run, parsed, and the packages that hold them, each by
||| its path and text, so that a change can reach a module's importers and
||| the package that lists it.
module Lint.Refactor.Project

import Lint.Refactor.Subject

import Data.Either
import Data.List
import Data.List1
import Data.String
import Lint.Resolution
import System.Directory
import System.File.Error
import System.File.ReadWrite

%default covering

||| The files of a run, parsed, and the packages beside its roots.
public export
record Project where
  constructor MkProject
  files : List Subject
  ||| Each package file by its path and text.
  packages : List (String, String)
  ||| What the modules use, resolved from their TTCs, as they were built
  ||| before the run, if they could be read.
  resolution : Maybe Resolution
  ||| The other modules of the packages beside the roots, parsed once before
  ||| the run: what a file of the run may import from outside the roots, read
  ||| for what it exports, never changed.
  context : List Subject

||| The packages in each root's directory and its parent, each by its path
||| and text: a package's sources are its directory or one below it.
export
packagesNear : (roots : List String) -> IO (List (String, String))
packagesNear roots = do
  let dirs = nub (concatMap (\r => [r, parentOf r]) roots)
  packages <- traverse packagesIn dirs
  pure (nub (concat packages))
  where
    ||| A path in a directory, the current one written as nothing.
    inDirectory : String -> String -> String
    inDirectory "" f = f
    inDirectory d f = d ++ "/" ++ f

    packagesIn : String -> IO (List (String, String))
    packagesIn d = do
      Right names <- listDir (if d == "" then "." else d)
        | Left _ => pure []
      texts <- traverse (\n => map (inDirectory d n,) <$> readFile (inDirectory d n))
        (filter (isSuffixOf ".ipkg") names)
      pure (rights texts)

    ||| A directory's parent, `""` for the current one.
    parentOf : String -> String
    parentOf p = case reverse (List1.forget (split (== '/') p)) of
      (_ :: rest@(_ :: _)) => joinBy "/" (reverse rest)
      _ => ""

||| The files of a run, parsed, the packages beside its roots, and the
||| context, parsed before.
export
loadProject : (roots, paths : List String) -> Maybe Resolution -> (context : List Subject) ->
              IO Project
loadProject roots paths res context = do
  subjects <- traverse load paths
  packages <- packagesNear roots
  pure (MkProject (rights subjects) packages res context)

||| Where a package keeps its sources: its `sourcedir` under its directory,
||| its directory if it names none or `.`.
export
sourceDirOf : (path, text : String) -> String
sourceDirOf path text =
  let dir = parentOf path in
  case mapMaybe value (lines text) of
    (d :: _) => if d == "." || d == "" then dir else (if dir == "" then d else dir ++ "/" ++ d)
    [] => dir
  where
    parentOf : String -> String
    parentOf p = case reverse (List1.forget (split (== '/') p)) of
      (_ :: rest@(_ :: _)) => joinBy "/" (reverse rest)
      _ => ""

    value : String -> Maybe String
    value l = case break (== '=') (unpack (trim l)) of
      (k, '=' :: v) => if trim (pack k) == "sourcedir"
        then Just (pack (filter (/= '"') (unpack (trim (pack v))))) else Nothing
      _ => Nothing
