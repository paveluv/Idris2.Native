||| How a module of ours writes a name another of ours defines
||| (`pathQualifier`): with the defining module's path past what the two
||| modules' names share. One rule, which the refactoring `qualify-names`
||| writes by and `import-alias` checks.
|||
||| In `Native.Codegen.RegAlloc`, `SWord` of `Native.Codegen.TermIR.StaticDef`
||| is `TermIR.StaticDef.SWord`, `piece` of `Data.Builder` is
||| `Data.Builder.piece`. A type named after its module drops the module's
||| name: `TermIR.StaticDef`, which Idris resolves only through an alias,
||| the module imported under the path's rest (`as TermIR`); a peer's type,
||| of the same group, is bare (`Target`). So does the type's constructor
||| `MkX`, named after it: `TermIR.MkStaticDef`, and a peer's bare
||| (`MkPort`). Every other name keeps the whole path.
module Lint.Qualifier

import Data.List
import Data.List1
import Data.String

%default covering

||| A module's path seen from another module: its name past the parts the
||| two names begin with alike; its own last name if that leaves nothing.
export
pathFrom : (importer, defining : String) -> List String
pathFrom importer m = case dropShared (nameParts importer) (nameParts m) of
  [] => maybe [] (\x => [x]) (last' (nameParts m))
  rest => rest
  where
    dropShared : List String -> List String -> List String
    dropShared (a :: as) (b :: bs) = if a == b then dropShared as bs else b :: bs
    dropShared _ bs = bs

    ||| The parts of a dotted name.
    nameParts : String -> List String
    nameParts m = forget (split (== '.') m)

||| Whether a name is a module's key type, of its last name `m`, or the
||| type's constructor, `MkX` for `X`.
export
keyNamed : (m, name : String) -> Bool
keyNamed m n = n == m || n == "Mk" ++ m

||| The qualifier a name defined in a module at the path is written with,
||| if any: the path, or, for the module's key type and its constructor
||| `MkX` (`keyNamed`), the path but its last part, none if that leaves
||| nothing.
export
pathQualifier : (path : List String) -> (name : String) -> Maybe String
pathQualifier path n = case reverse path of
  (m :: rest) =>
    if keyNamed m n then (if null rest then Nothing else Just (joinBy "." (reverse rest)))
    else Just (joinBy "." path)
  [] => Nothing

||| A name as written with its qualifier.
export
qualifiedName : (path : List String) -> (name : String) -> String
qualifiedName path n = maybe n (\q => q ++ "." ++ n) (pathQualifier path n)

||| The alias the module at a path is imported under where its key type is
||| written: the path but its last part, if more than that is left.
export
aliasAt : (path : List String) -> Maybe String
aliasAt path = case reverse path of
  (_ :: rest@(_ :: _)) => Just (joinBy "." (reverse rest))
  _ => Nothing
