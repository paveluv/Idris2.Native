||| The rules over what our modules use, resolved from their TTCs, and the
||| components of the health score they measure.
|||
||| A module imports directly what it uses: a module used but reached only
||| through another's re-export is a finding, whoever re-exports it, a
||| package's module, a façade or another of ours; only what the implicit
||| `Prelude` re-exports needs no import. And an import that gives the
||| module nothing it does not import directly is a finding.
module Lint.ResolvedRules

import Lint.Finding
import Lint.Graph
import Lint.Precision
import Lint.Resolution
import Lint.Rules
import Lint.Separation
import Lint.Source

import Core.FC
import Core.Name
import Core.Name.Namespace
import Core.TT
import Core.WithData
import Data.List
import Data.List1
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Data.String
import Idris.Syntax
import Libraries.Data.WithData
import Libraries.Data.WithDefault

%default covering

||| What a private import gives the module.
data Usage
  = ||| Something the module uses that no other of its imports gives it
    ||| directly: the imported module's own, or one it re-exports.
    Needed
  | ||| Only what the module also imports directly: the modules named.
    Redundant (List String)
  | ||| Nothing the module uses.
    Unused

||| One of our modules with what its text writes and what it uses, as the
||| rules over it see it.
record Linted where
  constructor MkLinted
  file : SourceFile
  resolved : ResolvedModule
  ||| The other modules whose names the module's text writes, or whose
  ||| implementations it uses, found by search, each with the names.
  writtenUses : SortedMap String (List String)
  ||| The modules it may use: those it imports, and those the implicit
  ||| `Prelude` re-exports, which no module imports. Any other re-export,
  ||| a package's, a façade's or one of our modules', is not leaned on: a
  ||| module imports directly what it uses.
  reached : SortedSet String
  ||| The types it defines.
  types : List String
  ||| Its private imports, each with what it gives the module: of what it
  ||| makes visible, what the module refers to, written or not (a type an
  ||| implicit argument names, an implementation found by search), and
  ||| whether another import gives that directly.
  privateImports : List (Import, Usage)

||| Our modules, each with its file and what it writes.
modulesOf : List (SourceFile, List Declared, Mentions) -> Resolution -> List Linted
modulesOf fms r =
  let byPath = the (SortedMap String ResolvedModule) (fromList (map (\rm => (rm.path, rm)) r.modules))
  in mapMaybe (one byPath) fms
  where
    one : SortedMap String ResolvedModule -> (SourceFile, List Declared, Mentions) -> Maybe Linted
    one byPath (f, ds, ms) = case lookup f.path byPath of
      Nothing => Nothing
      Just rm =>
        let written = the (SortedSet String) (fromList (map (\(_, n) => nameRoot n) ms.refs))
            ws = foldl (\acc, u => if u.searched || contains u.name written then insert u.definer (u.name :: fromMaybe [] (lookup u.definer acc)) acc else acc)
                       empty rm.uses
            used = the (SortedSet String) (fromList (map (.definer) rm.uses))
            reached = foldl Data.SortedSet.union empty
                            (map (\(i, _) => if i == "Prelude" then visibleThrough r.importsOf (const True) i else singleton i) rm.imports)
            direct = the (SortedSet String) (fromList (map (show . (.path)) f.mod.imports))
            usage : String -> Usage
            usage p = case filter (\v => contains v used) (Prelude.toList (visibleThrough r.importsOf (const True) p)) of
              [] => Unused
              vs => if any (\v => v == p || not (contains v direct)) vs then Needed else Redundant vs
            privates = [ (i, usage (show i.path)) | i <- f.mod.imports, not i.reexport ]
        in Just (MkLinted f rm ws reached (typesOf ds) privates)

------------------------------------------------------------------------------
-- The rules

||| The names of the rules over the program resolved, which run only when
||| it is.
export
resolvedRuleNames : List String
resolvedRuleNames = ["import-unused", "import-indirect", "generic-export", "public-unneeded", "raw-maker", "sealed-allocator"]

||| The rules whose suppression covers one use, the first after it: each
||| use is to say why it is sound by itself.
export
oneUseRules : List String
oneUseRules = ["sealed-allocator"]

||| The rules over the program resolved.
export
resolvedRules : List (SourceFile, List Declared, Mentions) -> (programNames : SortedSet String) -> Resolution -> List Finding
resolvedRules fms programNames r =
  joined [ importUnused m ++ importIndirect r m ++ genericExport m | m <- modulesOf fms r ]
  ++ joined [ publicUnneeded f ds ++ rawMaker f ++ sealedAllocator f ms | (f, ds, ms) <- fms ]
  where
    ||| `sealed-allocator`: outside the allocator's modules
    ||| (`Native.Runtime.Alloc.`), a use of any of their names but the
    ||| linear blocks' (`Alloc.Block`): the allocator's own functions, which
    ||| take and give addresses as words, and the two that turn a block into
    ||| a word and back. Each is a place the types no longer check that a
    ||| block is freed once, so each is to say why it is sound. Every
    ||| mention of such a name in the file is reported, where it is written.
    sealedAllocator : SourceFile -> Mentions -> List Finding
    sealedAllocator f ms =
      let m = show f.mod.moduleNS in
      if isPrefixOf "Native.Runtime.Alloc." m then [] else
        let sealed = the (SortedSet String) (fromList
              [ u.name | rm <- r.modules, rm.path == f.path, u <- rm.uses, leaves u ])
        in [ finding f "sealed-allocator" fc (nameRoot n)
               ("`" ++ nameRoot n ++ "` leaves the linear blocks of `Native.Runtime.Alloc.Block`: say why it is sound")
           | (fc, n) <- ms.refs, contains (nameRoot n) sealed ]
      where
        ||| What the blocks' module gives that the types check.
        linear : List String
        linear = ["Block", "Addressed", "MkAddressed", "allocate", "address", "free"]

        ||| Whether a use is of the allocator's modules, and not of the
        ||| blocks that the types check.
        leaves : Use -> Bool
        leaves u = isPrefixOf "Native.Runtime.Alloc." u.definer
                   && not (u.definer == "Native.Runtime.Alloc.Block" && any (== u.name) linear)

    ||| `raw-maker`: a raw address made from a word (`Raw.fromWord`) outside
    ||| the modules that keep addresses as words or are given them so: the
    ||| memory module, the state, the spaces (the collector's interface holds
    ||| addresses as words), the allocator's page source (`Pages` holds them
    ||| so too) and the platforms (the system gives its results as words). Elsewhere a raw address comes from an operation that gives
    ||| one, so a count is not taken for an address.
    rawMaker : SourceFile -> List Finding
    rawMaker f =
      let m = show f.mod.moduleNS in
      if elem m makers || isPrefixOf "Native.Runtime.OS." m then [] else
        [ finding f "raw-maker" f.mod.headerLoc u.name
            ("`" ++ m ++ "` makes a raw address from a word, which only the modules that keep addresses as words do")
        | rm <- r.modules, rm.name == m, u <- rm.uses, u.name == "fromWord", u.definer == "Native.Runtime.Raw" ]
      where
        makers : List String
        makers = ["Native.Runtime.Raw", "Native.Runtime.Memory", "Native.Runtime.State", "Native.Runtime.Space", "Native.Runtime.Alloc.System"]

    ||| `public-unneeded`: a `public export` that only its module
    ||| needs public. A data type whose constructors no other module uses
    ||| (resolved) and no program writes could be `export`, the type kept and
    ||| its constructors not; a function or constant no other module uses
    ||| needs no body public, if a name exported at all. Either is needed
    ||| public when another public declaration of its module mentions it,
    ||| since that one's body is visible to importers.
    publicUnneeded : SourceFile -> List Declared -> List Finding
    publicUnneeded f ds =
      let m = show f.mod.moduleNS
          usedElsewhere = the (SortedSet String) (fromList [ u.name | rm <- r.modules, rm.name /= m, u <- rm.uses, u.definer == m ])
          publicNames = joined (map (.defines) (filter isPublicClaim ds))
          inPublic = [ n | d <- ds, isPublicDecl publicNames d, n <- d.mentions, not (n `elem` d.defines) ]
          needed = \n => contains n usedElsewhere || contains n programNames || (n `elem` inPublic)
      in joined (map (finding' needed) ds)
      where
        publicVisibility : WithDefault Visibility Private -> Bool
        publicVisibility v = collapseDefault v == Public

        isPublicClaim : Declared -> Bool
        isPublicClaim d = case d.decl.val of
          PClaim c => c.vis == Public
          _ => False

        -- a public declaration whose body its importers see: a public
        -- claim's definition, or a public type
        isPublicDecl : List String -> Declared -> Bool
        isPublicDecl publicNames d = case d.decl.val of
          PDef _ => any (`elem` publicNames) d.defines
          PData _ v _ _ => publicVisibility v
          PRecord _ v _ _ => publicVisibility v
          _ => False

        finding' : (String -> Bool) -> Declared -> List Finding
        finding' needed d = case d.decl.val of
          PData _ v _ (MkPData _ n _ _ cons@(_ :: _)) =>
            let names = foldr (\c, rest => map (nameRoot . (.val) . snd) (List1.forget c.val.names) ++ rest) [] cons in
            if publicVisibility v && not (any needed names)
              then [finding f "public-unneeded" d.decl.fc (nameRoot n)
                      ("`" ++ nameRoot n ++ "`'s constructors are used only in its module: `export` keeps them there")]
              else []
          PClaim c =>
            if c.vis == Public && not (any needed d.defines)
              then [ finding f "public-unneeded" d.decl.fc n ("no other module uses `" ++ n ++ "`: its body need not be public")
                   | n <- d.defines ]
              else []
          _ => []

    ||| `import-unused`: a private import that gives the module nothing it does
    ||| not import directly: none of the names it makes visible used, neither
    ||| the module's own nor any it re-exports, or only those of modules
    ||| imported directly too. A façade's imports are for its importers, and so
    ||| is a public import: neither is reported.
    importUnused : Linted -> List Finding
    importUnused m = if facade m.file then [] else mapMaybe report m.privateImports
      where
        report : (Import, Usage) -> Maybe Finding
        report (_, Needed) = Nothing
        report (i, Redundant vs) =
          Just (finding m.file "import-unused" i.loc (show i.path)
                  ("`" ++ show i.path ++ "` is imported, and of what it makes visible only "
                   ++ listed vs ++ " is used, which the module imports directly"))
        report (i, Unused) =
          Just (finding m.file "import-unused" i.loc (show i.path)
                  ("`" ++ show i.path ++ "` is imported, and nothing it makes visible is used"))

    ||| `import-indirect`: a module whose names the module writes, or whose
    ||| implementations it uses, reached only through another module
    ||| re-exporting it. Search finds an implementation only where its module
    ||| is visible, so a module that uses one imports its module, as it does
    ||| one whose names it writes.
    importIndirect : Resolution -> Linted -> List Finding
    importIndirect r m = mapMaybe report (SortedMap.toList m.writtenUses)
      where
        through : String -> Maybe Import
        through u = find (\i => contains u (visibleThrough r.importsOf (const True) (show i.path))) m.file.mod.imports

        report : (String, List String) -> Maybe Finding
        report (u, ns) =
          if contains u m.reached then Nothing else
            let names = fastConcat (intersperse ", " (map (\n => "`" ++ n ++ "`") (take 3 (nub ns))))
                via = through u
                how = maybe "without importing it" (\i => "only through `" ++ show i.path ++ "`") via
            in Just (finding m.file "import-indirect" (maybe EmptyFC (.loc) via) u
                       ("`" ++ u ++ "` is used (" ++ names ++ ") " ++ how ++ ": import it"))

    ||| `generic-export`: in a module named after a type it defines,
    ||| an exported function whose type and body refer to nothing of ours, its
    ||| own recursion aside, and write no string, is a generic helper. (A string
    ||| names something, a namespace or a symbol: a function that writes one,
    ||| such as a routine's name, is a fact of its module.) A reader who wants it looks
    ||| for it among helpers, not in a module about a type, and writes it again
    ||| when it is not there: it belongs private to the module, or in a module
    ||| of helpers. A constant, which takes no arguments, is a fact of its
    ||| module, and is left out.
    genericExport : Linted -> List Finding
    genericExport m =
      if not aboutAType then [] else
        [ MkFinding "generic-export" m.file.path line col name
            ("`" ++ name ++ "` is exported from `" ++ m.resolved.name ++ "`, a module about its type, and refers to nothing of ours: a generic helper, private to the module or in a module of helpers")
        | (name, line, col) <- m.resolved.generics ]
      where
        -- whether the module is named after a type it defines
        aboutAType : Bool
        aboutAType = any (\t => toLower t == toLower (lastPart (show m.file.mod.moduleNS))) m.types

------------------------------------------------------------------------------
-- Health

||| The components the resolution measures: of the other modules whose names
||| our modules write, the share imported directly; of the private imports,
||| the share needed; and of the
||| accumulations, the share written with the structure their shape asks
||| for, a snoc-list or a builder, rather than lists.
export
resolvedHealth : List (SourceFile, List Declared, Mentions) -> Resolution -> List Component
resolvedHealth fms r =
  let fds = map (\(f, ds, _) => (f, ds)) fms
      ms = modulesOf fms r
      pairs = joined [ map (m,) (keys m.writtenUses) | m <- ms ]
      indirect = [ (m, u) | (m, u) <- pairs, not (contains u m.reached) ]
      imports = joined [ map (m,) m.privateImports | m <- ms, not (facade m.file) ]
      unneeded = [ (m, i, u) | (m, (i, u)) <- imports, not (needed u) ]
      unstructured = sum [ a.atEnd + a.leftFolds | m <- ms, a <- m.resolved.accumulations ]
      structured = sum [ a.structured | m <- ms, a <- m.resolved.accumulations ]
  in [ precision fds r, separation fds r
     , MkComponent "structure" "directness" (percent (minus (length pairs) (length indirect)) (length pairs))
         ("modules used that are imported directly: " ++ show (minus (length pairs) (length indirect)) ++ " of " ++ show (length pairs))
         [ MkOffender m.resolved.name 1 ("uses `" ++ u ++ "` through another's re-export") | (m, u) <- indirect ]
     , MkComponent "structure" "leanness" (percent (minus (length imports) (length unneeded)) (length imports))
         ("private imports needed: " ++ show (minus (length imports) (length unneeded)) ++ " of " ++ show (length imports))
         [ MkOffender m.resolved.name 1 ("imports `" ++ show i.path ++ "` and " ++ uses u) | (m, i, u) <- unneeded ]
     , MkComponent "efficiency" "accumulation" (percent structured (structured + unstructured))
         ("accumulations in a snoc-list or a builder: " ++ show structured ++ " of " ++ show (structured + unstructured))
         [ MkOffender (m.resolved.name ++ "." ++ a.subject) (a.atEnd + a.leftFolds)
             (show a.atEnd ++ " grown at an end with `++`, " ++ show a.leftFolds ++ " joined by a left fold")
         | m <- ms, a <- m.resolved.accumulations, a.atEnd + a.leftFolds > 0 ] ]
  where
    needed : Usage -> Bool
    needed Needed = True
    needed _ = False

    uses : Usage -> String
    uses (Redundant vs) = "uses of it only " ++ listed vs ++ ", which it imports directly"
    uses _ = "uses nothing it makes visible"
