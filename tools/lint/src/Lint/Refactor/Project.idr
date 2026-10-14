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

||| The files of a run, parsed, and the packages in each root's directory and
||| its parent: a package's sources are its directory or one below it.
export
loadProject : (roots, paths : List String) -> IO Project
loadProject roots paths = do
  subjects <- traverse load paths
  let dirs = nub (concatMap (\r => [r, parentOf r]) roots)
  packages <- traverse packagesIn dirs
  pure (MkProject (rights subjects) (nub (concat packages)))
  where
    ||| A path in a directory, the current one written as nothing.
    inDirectory : String -> String -> String
    inDirectory "" f = f
    inDirectory d f = d ++ "/" ++ f

    packagesIn : String -> IO (List (String, String))
    packagesIn d = do
      Right names <- listDir (if d == "" then "." else d)
        | Left _ => pure []
      texts <- traverse (\n => map (inDirectory d n,) <$> readFile (inDirectory d n)) (filter (isSuffixOf ".ipkg") names)
      pure (rights texts)

    ||| A directory's parent, `""` for the current one.
    parentOf : String -> String
    parentOf p = case reverse (List1.forget (split (== '/') p)) of
      (_ :: rest@(_ :: _)) => joinBy "/" (reverse rest)
      _ => ""
