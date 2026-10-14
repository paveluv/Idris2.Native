||| What our modules use, resolved: read from the TTCs the build wrote, where
||| every name carries the module that defines it, so that what a module
||| needs is known, and not only what its text names. A module's uses are
||| the names its definitions refer to (their types and their bodies, an
||| implementation found by search included), by the modules that define
||| them.
|||
||| A module's TTC is found beside its package: the package of a source
||| root is the root's directory, or its parent, whichever holds an `.ipkg`,
||| and its TTCs are in that directory's `build/ttc`. The modules our
||| modules import come from there too, when they are ours, and otherwise
||| from the installed packages.
module Lint.Resolution

import Core.Binary
import Core.Binary.Prims
import Core.Case.CaseTree
import Core.Context
import Core.Context.Context
import Core.Core
import Core.Directory
import Core.Env
import Core.FC
import Core.Name
import Core.Name.Namespace
import Core.Options
import Core.TT
import Core.TT.Binder
import Core.TT.Primitive
import Core.TT.Term
import Core.TTC
import Core.UnifyState
import Data.List
import Data.List1
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Data.String
import Data.Zippable
import Idris.Package.Types
import Idris.ProcessIdr
import Idris.SetOptions
import Idris.Syntax
import Libraries.Data.NameMap
import Libraries.Data.WithDefault
import Libraries.Utils.Binary
import Libraries.Utils.Path
import Lint.Finding
import Lint.Source
import System
import System.Directory
import System.File
import System.File.Meta

%default covering

------------------------------------------------------------------------------
-- What is resolved

||| A definition's accumulations, in all its clauses' terms, erased parts
||| included: how many grow a list at its end with `++` (a recursive call,
||| or a left fold's step, given a variable the clause matched with more
||| appended), how many join lists by a left fold (`concat`, `concatMap` or
||| `foldMap` at a list's monoid), and how many are written with the
||| structure their shape asks for (a snoc-list's `:<` or `<><`, a join at a
||| `Builder`'s monoid).
public export
record Accumulations where
  constructor MkAccumulations
  ||| The definition, by its name as written: a `where` function's own, a
  ||| `case` block's that of the definition it is in.
  subject : String
  line : Int
  col : Int
  atEnd : Nat
  leftFolds : Nat
  structured : Nat

||| A name a module's definitions refer to: the module that defines it, the
||| name without its namespace (an implementation by what it implements,
||| `Show Shape`), and whether it is an implementation, which the module
||| uses without writing it, found by search.
public export
record Use where
  constructor MkUse
  definer : String
  name : String
  searched : Bool

||| One of our modules, resolved: its imports, each with whether it is
||| public; the names its definitions refer to, the module's own left out;
||| and its definitions' accumulations.
public export
record ResolvedModule where
  constructor MkResolvedModule
  name : String
  path : String
  imports : List (String, Bool)
  uses : List Use
  accumulations : List Accumulations
  ||| Its exported functions, those that take arguments, whose types and
  ||| bodies refer to nothing of ours but themselves and write no string:
  ||| each by its name and where it is.
  generics : List (String, Int, Int)

||| The program resolved: our modules, and the imports of every module
||| loaded, ours and those of the packages, to follow their re-exports.
public export
record Resolution where
  constructor MkResolution
  modules : List ResolvedModule
  importsOf : SortedMap String (List (String, Bool))

||| What a module makes visible to its importers: itself, and what it
||| re-exports publicly, in turn, re-exports followed where `follow` says.
export
visibleThrough : SortedMap String (List (String, Bool)) -> (follow : String -> Bool) -> String -> SortedSet String
visibleThrough imports follow m = go empty [m]
  where
    go : SortedSet String -> List String -> SortedSet String
    go acc [] = acc
    go acc (i :: is) =
      if contains i acc then go acc is
      else let next = if follow i then map (\(j, _) => j) (filter (\(_, reexported) => reexported) (fromMaybe [] (lookup i imports))) else [] in
           go (insert i acc) (next ++ is)

------------------------------------------------------------------------------
-- Names

------------------------------------------------------------------------------
-- Accumulations

||| What a semigroup or monoid joins: lists, builders, or other things.
data Joins = JoinsLists | JoinsBuilders | JoinsOther

Eq Joins where
  JoinsLists == JoinsLists = True
  JoinsBuilders == JoinsBuilders = True
  JoinsOther == JoinsOther = True
  _ == _ = False

||| The label of the accumulations being counted, and of what is known of
||| the implementations met.
data Counting : Type where

record Count where
  constructor MkCount
  atEnd : Nat
  leftFolds : Nat
  structured : Nat
  joins : SortedMap String Joins

||| How a definition calls itself, for telling an accumulation: by its own
||| name, with each argument's pattern in the clause when it is a variable
||| (its index in the clause's environment), so that an argument is compared
||| with the pattern in its place; or, from a `case` or `with` block, by the
||| name of the definition the block is part of, whose arguments the
||| block's do not line up with.
data Recursion = Own Name (List (Maybe Nat)) | FromBlock (Name -> Bool)

------------------------------------------------------------------------------
-- Resolving

||| Our modules resolved from their TTCs, or the findings of those whose TTCs
||| are missing or older than their sources, or why the TTCs did not load.
export
resolve : List SourceFile -> IO (Either (List Finding) Resolution)
resolve fs = coreRun run (\err => pure (Left [MkFinding "resolution" "" 0 0 "" (show err)])) pure
  where
    ||| A file's module as a path, without its extension.
    modulePath : SourceFile -> String
    modulePath f = fastConcat (intersperse "/" (reverse (unsafeUnfoldNamespace (miAsNamespace f.mod.moduleNS))))

    ||| The directory of the TTCs of a source file's package, if its path ends as
    ||| its module's name says: Idris looks for them under it, in the
    ||| directory of its TTC version.
    ttcDirectory : SourceFile -> IO (Maybe String)
    ttcDirectory f =
      let rel = modulePath f ++ ".idr" in
      if not (isSuffixOf rel f.path) then pure Nothing else do
        let root = substr 0 (minus (length f.path) (length rel)) f.path
            dir = if root == "" then "." else pack (dropTrailingSlash (unpack root))
        pkg <- packageOf dir
        pure (Just (pkg ++ "/build/ttc"))
      where
        dropTrailingSlash : List Char -> List Char
        dropTrailingSlash cs = reverse (dropWhile (== '/') (reverse cs))

        ||| The directory holding a source root's package: the root, or its parent,
        ||| whichever holds an `.ipkg`; the root when neither does.
        packageOf : String -> IO String
        packageOf root = do
          here <- hasPackage root
          if here then pure root else do
            let up = parentOf root
            there <- hasPackage up
            pure (if there then up else root)
          where
            hasPackage : String -> IO Bool
            hasPackage d = do
              Right es <- listDir d
                | Left _ => pure False
              pure (any (isSuffixOf ".ipkg") es)

            ||| A path's directory, `.` for none.
            directoryOf : String -> String
            directoryOf p = case reverse (forget (Data.String.split (== '/') p)) of
              (_ :: d@(_ :: _)) => fastConcat (intersperse "/" (reverse d))
              _ => "."

            parentOf : String -> String
            parentOf "." = ".."
            parentOf d = directoryOf d

    ||| Whether a file's TTC is there and newer than its source; a finding
    ||| otherwise.
    fresh : SourceFile -> String -> Core (Maybe Finding)
    fresh f dir = do
      let ttc = dir ++ "/" ++ show ttcVersion ++ "/" ++ modulePath f ++ ".ttc"
      built <- modTime ttc
      written <- modTime f.path
      let problem = \m => Just (MkFinding "resolution" f.path 0 0 (show f.mod.moduleNS) m)
      pure (if built == MkTimestamp 0 0 then problem ("no TTC for `" ++ show f.mod.moduleNS ++ "` in " ++ dir ++ ": build it first")
            else if built < written then problem ("the TTC of `" ++ show f.mod.moduleNS ++ "` is older than its source: build it first")
            else Nothing)

    inModule : String -> String -> Name
    inModule m n = NS (mkNamespace m) (UN (Basic n))

    ||| The methods that join by a semigroup or monoid, each with the positions
    ||| of its arguments that are the semigroup's or monoid's implementation.
    joiners : {auto c : Ref Ctxt Defs} -> Core (List (Name, List Nat))
    joiners = do
      defs <- get Ctxt
      traverse (positions defs) [ inModule "Prelude.Interfaces" m | m <- ["<+>", "concat", "concatMap", "foldMap"] ]
      where
        joinInterface : Defs -> Term vs -> Core Bool
        joinInterface defs ty = case getFnArgs ty of
          (Ref _ _ n, _) => do
            n' <- full (gamma defs) n
            pure (n' == inModule "Prelude.Interfaces" "Semigroup" || n' == inModule "Prelude.Interfaces" "Monoid")
          _ => pure False

        go : Defs -> Nat -> Term vs -> Core (List Nat)
        go defs i (Bind _ _ (Pi _ _ AutoImplicit ty) sc) = do
          here <- joinInterface defs ty
          rest <- go defs (S i) sc
          pure (if here then i :: rest else rest)
        go defs i (Bind _ _ (Pi _ _ _ _) sc) = go defs (S i) sc
        go _ _ _ = pure []

        positions : Defs -> Name -> Core (Name, List Nat)
        positions defs n = do
          Just g <- lookupCtxtExact n (gamma defs)
            | Nothing => pure (n, [])
          (n,) <$> go defs 0 g.type

    ||| Idris set up as its driver sets it up from the environment, the parts the
    ||| linter needs: the prefix, the directories of TTCs and of packages, and
    ||| the installed packages; then the directories of our TTCs, searched
    ||| before them.
    setUp : {auto c : Ref Ctxt Defs} -> List String -> Core ()
    setUp ours = do
      root <- coreLift (getEnv "IDRIS2_PREFIX")
      whenJust root setPrefix
      ttcs <- coreLift (getEnv "IDRIS2_PATH")
      whenJust ttcs (traverse_ addExtraDir . paths)
      packageDirs <- coreLift (getEnv "IDRIS2_PACKAGE_PATH")
      whenJust packageDirs (traverse_ addPackageSearchPath . paths)
      addPackageSearchPath !pkgGlobalDirectory
      traverse_ (\p => catch (addPkgDir p anyBounds) (const (pure ()))) packages
      traverse_ addExtraDir ours
      where
        paths : String -> List String
        paths = filter (/= "") . map trim . forget . Data.String.split (== pathSeparator)

        ||| The packages a module of ours may import from, installed.
        packages : List String
        packages = ["prelude", "base", "contrib", "network", "idris2", "idris2-native", "idris2-native-runtime"]

    ||| A module's imports, each with whether it is public, read from the head
    ||| of its TTC, where they follow the hashes and the incremental data: the
    ||| context keeps which modules are loaded, not which imports which.
    importsOf : {auto c : Ref Ctxt Defs} -> String -> Core (List (String, Bool))
    importsOf m = do
      let mi = nsAsModuleIdent (mkNamespace m)
      Right path <- nsToPath EmptyFC mi
        | Left _ => pure []
      Right buffer <- coreLift (readFromFile path)
        | Left _ => pure []
      b <- newRef Bin buffer
      ignore (getHashes path b)
      ignore (fromBuf {a = List (Namespace, Int)})
      ignore (fromBuf {a = List (CG, String, List String)})
      is <- fromBuf {a = List (ModuleIdent, Bool, Namespace)}
      pure (map edge is)
      where
        edge : (ModuleIdent, Bool, Namespace) -> (String, Bool)
        edge (i, re, _) = (show i, re)

    ||| The module a name belongs to: the longest of the modules whose name
    ||| begins its namespace.
    moduleOfName : SortedSet String -> Name -> Maybe String
    moduleOfName mods (NS ns _) = longest (reverse (unsafeUnfoldNamespace ns))
      where
        longest : List String -> Maybe String
        longest [] = Nothing
        longest parts =
          let m = fastConcat (intersperse "." parts) in
          if contains m mods then Just m else longest (take (minus (length parts) 1) parts)
    moduleOfName _ _ = Nothing

    ||| A module of ours, resolved from the context it is loaded into.
    resolveModule : {auto c : Ref Ctxt Defs} -> {auto n : Ref Counting Count} ->
                    (ours : SortedSet String) -> SortedSet String -> SortedSet String -> List (Name, List Nat) -> (SourceFile, List Name) ->
                    Core ResolvedModule
    resolveModule ours mods implementations js (f, names) = do
      let m = show f.mod.moduleNS
      defs <- get Ctxt
      is <- importsOf m
      perName <- traverse (definition defs) names
      let uses = Prelude.toList (the (SortedSet (String, String, Bool)) (fromList (filter (\(u, _, _) => u /= m) (joined [ us | (us, _, _) <- perName ]))))
      pure (MkResolvedModule m f.path is (map (\(u, r, s) => MkUse u r s) uses)
              (mapMaybe (\(_, a, _) => a) perName) (mapMaybe (\(_, _, g) => g) perName))
      where
        -- the head of a type, as its name is written
        headOf : Defs -> Term vs -> Core String
        headOf defs t = case getFnArgs t of
          (Ref _ _ n, _) => nameRoot <$> full (gamma defs) n
          _ => pure "_"

        -- an implementation by what it implements, `Show Shape`: its type's
        -- interface and the heads of its arguments
        implemented : Defs -> Term vs -> Core String
        implemented defs (Bind _ _ (Pi _ _ _ _) sc) = implemented defs sc
        implemented defs t = case getFnArgs t of
          (Ref _ _ n, args) => do
            iface <- nameRoot <$> full (gamma defs) n
            heads <- traverse (headOf defs) args
            pure (unwords (iface :: heads))
          _ => pure "an implementation"

        used : Defs -> Name -> Core (Maybe (String, String, Bool))
        used defs r = do
          r' <- full (gamma defs) r
          let searched = contains (show r') implementations
          shown <- if not searched then pure (nameRoot r') else do
            Just g <- lookupCtxtExact r' (gamma defs)
              | Nothing => pure (nameRoot r')
            implemented defs g.type
          pure (map (\u => (u, shown, searched)) (moduleOfName mods r'))


        -- the explicit arguments a type takes
        arguments : Term vs -> Nat
        arguments (Bind _ _ (Pi _ _ Explicit _) sc) = S (arguments sc)
        arguments (Bind _ _ (Pi _ _ _ _) sc) = arguments sc
        arguments _ = Z

        -- a function at a module's top, or in a namespace block, by its own name
        atTop : Name -> Bool
        atTop (NS _ (UN (Basic _))) = True
        atTop _ = False

        ||| A name as shown, without its namespace, and, for a `case` or `with`
        ||| block, without the words before the name of the definition it is in,
        ||| perhaps a block itself: the definition whose clauses the block is part of.
        outermost : String -> String
        outermost s =
          let p = case last' (forget (Data.String.split (== '.') s)) of
                    Just p => p
                    Nothing => s
          in if isPrefixOf "case block in " p then outermost (substr 14 (length p) p)
             else if isPrefixOf "with block in " p then outermost (substr 14 (length p) p)
             else p

        ||| A definition's name as written: a `where` function's own, a `case` or
        ||| `with` block's that of the definition it is in; none for a name the
        ||| elaborator made.
        writtenName : Name -> Maybe String
        writtenName (NS _ n) = writtenName n
        writtenName (UN n) = Just (displayUserName n)
        writtenName (Nested _ n) = writtenName n
        writtenName (CaseBlock outer _) = Just (outermost outer)
        writtenName (WithBlock outer _) = writtenName (CaseBlock outer 0)
        writtenName (DN _ n) = writtenName n
        writtenName _ = Nothing

        ||| Whether a term writes a string: a string names something, a namespace or
        ||| a symbol, and makes the definition a fact of its module.
        writesString : Term vs -> Bool
        writesString (PrimVal _ (Str _)) = True
        writesString (App _ f a) = writesString f || writesString a
        writesString (Bind _ _ b sc) = inBinder b || writesString sc
          where
            inBinder : Binder (Term vs) -> Bool
            inBinder (Let _ _ v _) = writesString v
            inBinder (PLet _ _ v _) = writesString v
            inBinder _ = False
        writesString (As _ _ _ p) = writesString p
        writesString (TDelayed _ _ t) = writesString t
        writesString (TDelay _ _ _ t) = writesString t
        writesString (TForce _ _ t) = writesString t
        writesString _ = False

        ||| A definition's accumulations, counted in the right-hand sides of its
        ||| clauses: at its end, by left folds, and structured.
        accumulationsOf : List (Name, List Nat) -> GlobalDef -> Core (Nat, Nat, Nat)
        accumulationsOf js g = do
          update Counting { atEnd := 0, leftFolds := 0, structured := 0 }
          defs <- get Ctxt
          me <- full (gamma defs) g.fullname
          case g.definition of
            PMDef _ _ _ _ pats => traverse_ (\(_ ** (_, lhs, rhs)) => countIn js (recursion me lhs) 0 rhs) pats
            _ => pure ()
          k <- get Counting
          pure (k.atEnd, k.leftFolds, k.structured)
          where
            block : Name -> Bool
            block (NS _ n) = block n
            block (CaseBlock _ _) = True
            block (WithBlock _ _) = True
            block _ = False

            variable : Term vs -> Maybe Nat
            variable (Local _ _ idx _) = Just idx
            variable _ = Nothing

            -- a name's last part as written: a `where` function's is shown as
            -- `outer,inner` where a block names it, and `i:j:inner` as its own
            lastWritten : Name -> String
            lastWritten n = case last' (forget (Data.String.split (\c => c == ',' || c == ':') (outermost (show n)))) of
              Just p => p
              Nothing => show n

            -- a call of the definition itself, or, from a block, of the definition
            -- whose clauses the block is part of
            recursion : Name -> Term vs -> Recursion
            recursion me lhs =
              if block me then FromBlock (\f => f == me || lastWritten f == lastWritten me)
              else Own me (map variable (snd (getFnArgs lhs)))

            ||| Count the accumulations in a term, `depth` binders inside a clause's
            ||| right-hand side.
            countIn : List (Name, List Nat) -> Recursion -> (depth : Nat) -> Term vs -> Core ()
            countIn js self d tm = case getFnArgs tm of
              (Ref _ _ f, args) => do
                defs <- get Ctxt
                f' <- full (gamma defs) f
                note f' args
                traverse_ (countIn js self d) args
              (f, args) => do
                inner f
                traverse_ (countIn js self d) args
              where
                -- a variable the clause matched: bound outside the right-hand side's
                -- own binders, its index in the clause's environment
                matched : Term vs' -> Maybe Nat
                matched (Local _ _ idx _) = if idx >= d then Just (minus idx d) else Nothing
                matched _ = Nothing

                ||| Whether a name is one of the list appends, `++` on lists or snoc-lists.
                listAppend : Name -> Bool
                listAppend f = f == NS (mkNamespace "Prelude.Types.List") (UN (Basic "++"))
                               || f == NS (mkNamespace "Prelude.Types.SnocList") (UN (Basic "++"))

                -- `x ++ e`: the variable `x` is, if the clause matched it, and whether
                -- `e` is a variable the clause matched too
                appendTo : Term vs' -> Core (Maybe (Nat, Bool))
                appendTo t = case getFnArgs t of
                  (Ref _ _ g, [_, x, e]) => do
                    defs <- get Ctxt
                    g' <- full (gamma defs) g
                    pure (if listAppend g' then map (\i => (i, isJust (matched e))) (matched x) else Nothing)
                  _ => pure Nothing

                -- an argument of a recursive call that grows the pattern in its place
                -- at its end; from a block, one that grows a matched variable with
                -- something that is not one
                grows : List (Maybe Nat) -> (Nat, Term vs) -> Core Bool
                grows pats (i, a) = do
                  r <- appendTo a
                  pure (case (r, getAt i pats) of
                          (Just (x, _), Just (Just p)) => x == p
                          _ => False)

                growsFromBlock : Term vs -> Core Bool
                growsFromBlock a = do
                  r <- appendTo a
                  pure (case r of
                          Just (_, eMatched) => not eMatched
                          Nothing => False)

                -- a left fold's step `\acc, x => acc ++ e`
                stepAppends : Term vs' -> Core Bool
                stepAppends (Bind _ _ (Lam _ _ _ _) (Bind _ _ (Lam _ _ _ _) body)) = case getFnArgs body of
                  (Ref _ _ g, [_, Local _ _ 1 _, _]) => do
                    defs <- get Ctxt
                    g' <- full (gamma defs) g
                    pure (listAppend g')
                  _ => pure False
                stepAppends _ = pure False

                count : (Count -> Count) -> Core ()
                count f = update Counting f

                ||| What the implementation an argument passes joins: the implementation
                ||| itself, or one it is made from (a monoid's semigroup), the solution of
                ||| a hole the elaborator left for it, which the TTC keeps as a definition
                ||| of its own, or one under binders the elaborator put around it.
                dictionary : Nat -> Term vs'' -> Core Joins
                dictionary Z _ = pure JoinsOther
                dictionary (S k) t = case getFnArgs t of
                  (Ref _ _ d, args) => do
                    defs <- get Ctxt
                    j <- joinsOf !(full (gamma defs) d)
                    if j /= JoinsOther then pure j else firstOf args
                  (Meta _ hole _ _, _) => do
                    defs <- get Ctxt
                    Just g <- lookupCtxtExact hole (gamma defs)
                      | Nothing => pure JoinsOther
                    case g.definition of
                      PMDef _ _ (STerm _ solution) _ _ => dictionary k solution
                      _ => pure JoinsOther
                  (Bind _ _ b sc, _) => do
                    j <- dictionary k sc
                    if j /= JoinsOther then pure j else case b of
                      Let _ _ v _ => dictionary k v
                      _ => pure JoinsOther
                  _ => pure JoinsOther
                  where
                    firstOf : List (Term vs'') -> Core Joins
                    firstOf [] = pure JoinsOther
                    firstOf (a :: as) = do
                      j <- dictionary k a
                      if j /= JoinsOther then pure j else firstOf as

                    ||| What an implementation of a semigroup or monoid joins, told by its type.
                    joinsOf : Name -> Core Joins
                    joinsOf impl = do
                      known <- get Counting
                      case lookup (show impl) known.joins of
                        Just j => pure j
                        Nothing => do
                          defs <- get Ctxt
                          j <- case !(lookupCtxtExact impl (gamma defs)) of
                            Nothing => pure JoinsOther
                            Just g => classify defs g.type
                          update Counting { joins $= insert (show impl) j }
                          pure j
                      where
                        classify : Defs -> Term vs' -> Core Joins
                        classify defs (Bind _ _ (Pi _ _ _ _) sc) = classify defs sc
                        classify defs t = case getFnArgs t of
                          (Ref _ _ iface, args) => do
                            iface' <- full (gamma defs) iface
                            if iface' /= inModule "Prelude.Interfaces" "Semigroup" && iface' /= inModule "Prelude.Interfaces" "Monoid"
                              then pure JoinsOther
                              else case map getFnArgs (last' args) of
                                Just (Ref _ _ ty, _) => do
                                  ty' <- full (gamma defs) ty
                                  pure (if ty' == inModule "Prelude.Basics" "List" || ty' == inModule "Prelude.Basics" "SnocList" then JoinsLists
                                        else if ty' == inModule "Data.Builder" "Builder" then JoinsBuilders
                                        else JoinsOther)
                                _ => pure JoinsOther
                          _ => pure JoinsOther

                firstJoin : List (Term vs) -> Core Joins
                firstJoin [] = pure JoinsOther
                firstJoin (x :: xs) = do
                  j <- dictionary 4 x
                  if j /= JoinsOther then pure j else firstJoin xs

                note : Name -> List (Term vs) -> Core ()
                note f args = do
                  grown <- the (Core (List Bool)) $ case self of
                    Own me pats => if f == me then traverse (grows pats) (zip [0 .. length args] args) else pure Nil
                    FromBlock outer => if outer f then traverse growsFromBlock args else pure Nil
                  count { atEnd $= (+ length (filter id grown)) }
                  when (f == inModule "Prelude.Interfaces" "foldl") $ do
                    steps <- traverse stepAppends args
                    count { atEnd $= (+ length (filter id steps)) }
                  when (f == NS (mkNamespace "Prelude.Basics") (UN (Basic ":<"))
                        || f == NS (mkNamespace "Prelude.Types.SnocList") (UN (Basic "<><"))) $
                    count { structured $= S }
                  case lookup f js of
                    Nothing => pure ()
                    Just ps => do
                      j <- firstJoin (mapMaybe (\p => getAt p args) ps)
                      case j of
                        JoinsLists => when (f /= inModule "Prelude.Interfaces" "<+>") $ count { leftFolds $= S }
                        JoinsBuilders => count { structured $= S }
                        JoinsOther => pure ()

                binder : Binder (Term vs) -> Core ()
                binder (Let _ _ v ty) = countIn js self d v
                binder (PLet _ _ v ty) = countIn js self d v
                binder _ = pure ()

                inner : Term vs -> Core ()
                inner (Bind _ _ b sc) = do binder b; countIn js self (S d) sc
                inner (As _ _ a p) = countIn js self d p
                inner (TDelayed _ _ t) = countIn js self d t
                inner (TDelay _ _ _ a) = countIn js self d a
                inner (TForce _ _ t) = countIn js self d t
                inner _ = pure ()

        definition : Defs -> Name -> Core (List (String, String, Bool), Maybe Accumulations, Maybe (String, Int, Int))
        definition defs nm = do
          Just g <- lookupCtxtExact nm (gamma defs)
            | Nothing => pure ([], Nothing, Nothing)
          let refs = keys (fromMaybe empty g.refersToM) ++ keys (getRefs (UN Underscore) g.type) ++ clauseRefs g.definition
          us <- mapMaybe id <$> traverse (used defs) refs
          (atEnd, folds, structured) <- accumulationsOf js g
          let (line, col) = startOf g.location
          me <- full (gamma defs) nm
          resolvedRefs <- traverse (full (gamma defs)) refs
          let ofOurs = any (\r => r /= me && maybe False (\u => contains u ours) (moduleOfName mods r)) resolvedRefs
              isFunction = case g.definition of
                             PMDef _ _ _ _ _ => arguments g.type > 0
                             _ => False
              names = case g.definition of
                        PMDef _ _ _ _ pats => any (\(_ ** (_, _, rhs)) => writesString rhs) pats
                        _ => False
              generic = atTop me && collapseDefault g.visibility /= Private && isFunction
                        && not (contains (show me) implementations) && not ofOurs && not names
          pure (us, case writtenName nm of
                      Just s => if atEnd + folds + structured > 0 then Just (MkAccumulations s line col atEnd folds structured) else Nothing
                      Nothing => Nothing,
                    if generic then Just (nameRoot me, line, col) else Nothing)
          where
            -- what a definition's clauses name, the constructors its patterns
            -- match among them, which its references leave out
            clauseRefs : Def -> List Name
            clauseRefs (PMDef _ _ _ _ pats) =
              joined (map (\(_ ** (_, lhs, rhs)) => keys (getRefs (UN Underscore) lhs) ++ keys (getRefs (UN Underscore) rhs)) pats)
            clauseRefs _ = []

            startOf : FC -> (Int, Int)
            startOf (MkFC _ s _) = s
            startOf (MkVirtualFC _ s _) = s
            startOf EmptyFC = (0, 0)

    ||| Whether a name is not a data constructor.
    notConstructor : {auto c : Ref Ctxt Defs} -> Defs -> Name -> Core Bool
    notConstructor defs n = do
      Just g <- lookupCtxtExact n (gamma defs)
        | Nothing => pure True
      pure (case g.definition of
              DCon _ _ _ => False
              _ => True)

    run : Core (Either (List Finding) Resolution)
    run = do
      c <- newRef Ctxt !initDefs
      s <- newRef Syn initSyntax
      u <- newRef UST initUState
      dirs <- coreLift (traverse ttcDirectory fs)
      let located = mapMaybe (\(f, d) => map (f,) d) (zip fs dirs)
      problems <- mapMaybe id <$> traverse (\(f, d) => fresh f d) located
      if not (null problems) then pure (Left problems) else do
        setUp (Prelude.toList (the (SortedSet String) (fromList (map snd located))))
        traverse_ (\(f, _) => addImport (MkImport EmptyFC False f.mod.moduleNS (miAsNamespace f.mod.moduleNS))) located
        defs <- get Ctxt
        let mods = the (SortedSet String) (fromList (map (\(_, (m, _, _)) => show m) (allImported defs)))
        -- every name in the context, by the map from full names to their
        -- entries: `allNames` counts the entries from 1, and leaves out the
        -- first one
        let names = keys (resolvedAs (gamma defs))
        let ours = the (SortedSet String) (fromList (map (\(f, _) => show f.mod.moduleNS) located))
            byModule = foldl (\acc, nm => case moduleOfName mods nm of
                                 Just m => if contains m ours then insert m (nm :: fromMaybe [] (lookup m acc)) acc else acc
                                 Nothing => acc)
                             (the (SortedMap String (List Name)) empty) names
        -- the implementations, as Idris keeps them for search: by interface,
        -- and the hints of no interface; a data type's constructors are
        -- hints for it too, and are left out
        let hinted = joined (map (map (\(h, _) => h)) (values (typeHints defs))) ++ keys (autoHints defs)
        hintedNames <- traverse (full (gamma defs)) hinted
        found <- filterM (notConstructor defs) hintedNames
        let implementations = the (SortedSet String) (fromList (map show found))
        js <- joiners
        n <- newRef Counting (MkCount 0 0 0 empty)
        rs <- traverse (resolveModule ours mods implementations js)
                       [ (f, fromMaybe [] (lookup (show f.mod.moduleNS) byModule)) | (f, _) <- located ]
        imports <- traverse (\m => (m,) <$> importsOf m) (Prelude.toList mods)
        pure (Right (MkResolution rs (fromList imports)))
