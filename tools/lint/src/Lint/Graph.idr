||| The import graph of the modules linted together: the rules over it, and
||| the architectural health score.
|||
||| A module's layer is told by its name. Of our modules, a layer imports only
||| those of the layers below it; a module of no layer (a program, a test) may
||| import any. The runtime imports nothing from the libraries but what it
||| shares with the compiler.
module Lint.Graph

import Data.List
import Data.SortedMap
import Data.SortedSet
import Data.String
import Idris.Syntax
import Lint.Finding
import Lint.Rules
import Lint.Source

%default covering

------------------------------------------------------------------------------
-- Layers

||| The layers of the product, from the bottom: `Data` (structures any part
||| may use), `Flat` (the flat fragment, of no backend), `Native` (the code
||| generator), `Runtime` (the runtime library), and the linter's own.
data Layer = DataLayer | FlatLayer | NativeLayer | RuntimeLayer | LintLayer

Eq Layer where
  DataLayer == DataLayer = True
  FlatLayer == FlatLayer = True
  NativeLayer == NativeLayer = True
  RuntimeLayer == RuntimeLayer = True
  LintLayer == LintLayer = True
  _ == _ = False

layerOf : String -> Maybe Layer
layerOf m =
  if m == "Runtime" || isPrefixOf "Runtime." m then Just RuntimeLayer
  else if isPrefixOf "Compiler.Native." m then Just NativeLayer
  else if isPrefixOf "Flat." m then Just FlatLayer
  else if isPrefixOf "Lint." m then Just LintLayer
  else if isPrefixOf "Data." m then Just DataLayer
  else Nothing

||| The modules of other layers that a layer may import: a module of no layer
||| among ours (a program) by none, and the runtime only the two modules it
||| shares with the compiler.
mayImport : Layer -> String -> Bool
mayImport DataLayer m = False
mayImport FlatLayer m = layerOf m == Just DataLayer || layerOf m == Just FlatLayer
mayImport NativeLayer m = maybe False (\l => l == DataLayer || l == FlatLayer || l == NativeLayer) (layerOf m)
mayImport RuntimeLayer m = layerOf m == Just RuntimeLayer || m == "Compiler.Native.HeapObject" || m == "Flat.Uniform"
mayImport LintLayer m = layerOf m == Just LintLayer

||| Whether an import is allowed by the layers, given the modules that are
||| ours. The runtime may import nothing that is not ours.
allowed : SortedSet String -> (importer : String) -> (imported : String) -> Maybe Bool
allowed ours importer imported = case layerOf importer of
  Nothing => Nothing
  Just RuntimeLayer => Just (contains imported ours && mayImport RuntimeLayer imported)
  Just l => if contains imported ours then Just (mayImport l imported) else Nothing

moduleOf : SourceFile -> String
moduleOf f = show f.mod.moduleNS

||| The modules defined by the files.
ourModules : List SourceFile -> SortedSet String
ourModules fs = fromList (map moduleOf fs)

||| `layering` and `syscall`: imports the layers do not allow, and the raw
||| system call imported outside the platforms' modules.
export
graphRules : List SourceFile -> List Finding
graphRules fs =
  let ours = ourModules fs in
  foldr (\f, rest => rules ours f ++ rest) [] fs
  where
    rules : SortedSet String -> SourceFile -> List Finding
    rules ours f =
      [ MkFinding "layering" f.path (fst (start i.loc)) (snd (start i.loc)) imported
          ("`" ++ moduleOf f ++ "` may not import `" ++ imported ++ "`: the layers")
      | i <- f.mod.imports, let imported = show i.path, allowed ours (moduleOf f) imported == Just False ]
      ++
      [ MkFinding "syscall" f.path (fst (start i.loc)) (snd (start i.loc)) "Runtime.OS.Syscall"
          "the raw system call outside `Runtime.OS`: the platform's services reach the system"
      | i <- f.mod.imports, show i.path == "Runtime.OS.Syscall", not (isPrefixOf "Runtime.OS." (moduleOf f)) ]
      where
        start : FC -> (Int, Int)
        start (MkFC _ s _) = s
        start (MkVirtualFC _ s _) = s
        start EmptyFC = (0, 0)

------------------------------------------------------------------------------
-- Health

||| A share as a whole percentage; 100 when there is nothing to count.
percent : Nat -> Nat -> Nat
percent _ Z = 100
percent k n = let k' = the Integer (cast k); n' = the Integer (cast n) in
              cast ((200 * k' + n') `div` (2 * n'))

||| One component of the score: its name, its value, and what it counts.
public export
record Component where
  constructor MkComponent
  name : String
  value : Nat
  counted : String

||| The modules each module's imports reach, ours only.
reaches : SortedMap String (List String) -> String -> SortedSet String
reaches g m = go empty (fromMaybe [] (lookup m g))
  where
    go : SortedSet String -> List String -> SortedSet String
    go seen [] = seen
    go seen (n :: ns) =
      if contains n seen then go seen ns
      else go (insert n seen) (fromMaybe [] (lookup n g) ++ ns)

||| The components of the architectural health of the files' modules.
export
health : List SourceFile -> List Component
health fs =
  let ours = ourModules fs
      notFacades = filter (\f => not (all directive f.mod.decls)) fs
      imports = foldr (\f, rest => f.mod.imports ++ rest) [] notFacades
      privates = length (filter (not . (.reexport)) imports)
      checked = joined [ mapMaybe (\i => allowed ours (moduleOf f) (show i.path)) f.mod.imports | f <- fs ]
      good = length (filter id checked)
      g = fromList [ (moduleOf f, [ show i.path | i <- f.mod.imports, contains (show i.path) ours ]) | f <- fs ]
      n = length fs
      reached = sum [ length (Prelude.toList (reaches g (moduleOf f))) | f <- fs ]
  in [ MkComponent "encapsulation" (percent privates (length imports))
         ("private imports, façades exempt: " ++ show privates ++ " of " ++ show (length imports))
     , MkComponent "layering" (percent good (length checked))
         ("imports the layers allow: " ++ show good ++ " of " ++ show (length checked))
     , MkComponent "coupling" (percent (n * n `minus` reached) (n * n))
         ("module pairs a change cannot reach: " ++ show (n * n `minus` reached) ++ " of " ++ show (n * n)) ]
  where
    directive : PDecl -> Bool
    directive d = case d.val of
      PDirective _ => True
      _ => False

||| The score: the mean of the components.
export
score : List Component -> Nat
score [] = 100
score cs = percent (sum (map (.value) cs)) (100 * length cs)
