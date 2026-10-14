||| What one step of a refactoring does to the code (`Change`): edits to the
||| files it touches, the files it creates, and those it removes.
|||
||| One step may touch several files: a declaration moved to a module of its
||| own creates that module and edits the one it leaves and those that
||| import it.
module Lint.Refactor.Change

import Lint.Refactor.Edit

%default total

||| Edits, file by file, new files with their text, and files removed.
public export
record Change where
  constructor MkChange
  edits : List (String, List Edit)
  created : List (String, String)
  removed : List String

||| Edits to one file.
export
inFile : (path : String) -> List Edit -> Change
inFile path es = MkChange [(path, es)] [] []
