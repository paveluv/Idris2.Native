||| Where a package lists a module (`Listing`), and its list of modules as a
||| block a refactoring rewrites: what `split-module` adds to and
||| `join-modules` replaces entries of.
module Lint.Refactor.Listing

import Data.List
import Data.List1
import Data.String
import Data.Zippable

%default covering

||| Where a package lists a module, and the file a module made beside it
||| goes in: the package's path, the line of the module in its list, the
||| line's indentation, whether that line ends the list, and the new file's
||| path, under the package's `sourcedir`.
public export
record Listing where
  constructor MkListing
  package : String
  line : Int
  indent : String
  lastInList : Bool
  newPath : String

||| A line of a package's list as the module it names, without its comma.
entry : String -> String
entry l = let t = trim l in if isSuffixOf "," t then trim (substr 0 (minus (length t) 1) t) else t

||| The package that lists a module, and where a module named `new` goes in
||| it.
export
listingOf : List (String, String) -> (old, new : String) -> Either String Listing
listingOf packages old new = case mapMaybe listing packages of
  (l :: _) => Right l
  [] => Left ("no package lists `" ++ old ++ "`")
  where
    directoryOf : String -> String
    directoryOf p = case reverse (List1.forget (split (== '/') p)) of
      (_ :: rest@(_ :: _)) => joinBy "/" (reverse rest)
      _ => ""

    -- the package's `sourcedir`, `""` when it has none or it is `.`
    sourceDir : List String -> String
    sourceDir ls = case mapMaybe value ls of
      (d :: _) => if d == "." then "" else d
      [] => ""
      where
        value : String -> Maybe String
        value l = case break (== '=') (unpack (trim l)) of
          (k, '=' :: v) => if trim (pack k) == "sourcedir"
            then Just (pack (filter (/= '"') (unpack (trim (pack v))))) else Nothing
          _ => Nothing

    joinPath : List String -> String
    joinPath ps = joinBy "/" (filter (/= "") ps)

    listing : (String, String) -> Maybe Listing
    listing (path, text) =
      let ls = lines text
          numbered = zip [0 .. length ls] ls
      in case find (\(_, l) => entry l == old) numbered of
           Nothing => Nothing
           Just (i, l) =>
             Just
               (MkListing path (cast i) (pack (takeWhile (== ' ') (unpack l)))
                (not (isSuffixOf "," (trim l)))
                     (joinPath [directoryOf path,
                       sourceDir ls, joinBy "/" (List1.forget (split (== '.') new))] ++ ".idr"))

||| A package's list of modules: the lines it takes, both ends included, its
||| entries' indentation, and the modules in order.
public export
record ModuleList where
  constructor MkModuleList
  first : Int
  last : Int
  indent : String
  modules : List String

||| The list of modules of a package's text, if it has one: the entries
||| after `modules =`, up to the first line that is not one.
export
moduleList : String -> Maybe ModuleList
moduleList text =
  let ls = zip [0 .. length (lines text)] (lines text) in
  case dropWhile (not . heading . snd) ls of
    (_ :: rest) =>
      let entries = takeWhile (isEntry . snd) rest in
      case (entries, last' entries) of
        ((i, l) :: _, Just (j, _)) =>
          Just
            (MkModuleList (cast i) (cast j) (pack (takeWhile (== ' ') (unpack l)))
             (map (entry . snd) entries))
        _ => Nothing
    [] => Nothing
  where
    heading : String -> Bool
    heading l = isPrefixOf "modules" (trim l) && isSuffixOf "=" (trim l)

    isEntry : String -> Bool
    isEntry l = let t = trim l in t /= "" && isPrefixOf " " l
      && all (\c => isAlphaNum c || c == '.' || c == '_' || c == ',') (unpack t)

||| A list of modules as a package writes it: one a line, indented, each
||| but the last followed by a comma.
export
moduleLines : (indent : String) -> List String -> List String
moduleLines ind [] = []
moduleLines ind [m] = [ind ++ m]
moduleLines ind (m :: ms) = (ind ++ m ++ ",") :: moduleLines ind ms
