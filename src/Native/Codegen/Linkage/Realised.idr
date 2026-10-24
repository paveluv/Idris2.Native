||| The contract as the loaded runtime realises it (`Realised`): for each
||| entry, the function or the extern that is it (`realise`), not named by
||| the code generator.
|||
||| An inline extern is found by its type alone: the runtime declares each
||| as `PortTy (port c)` for its intrinsic `c` (`Native.Intrinsic`), which
||| Idris checks, and which the loaded context keeps as written. The
||| constructor `c` there is matched to the code generator's own by the
||| contract's list of every intrinsic: the list's term in the context and
||| the code generator's copy of it are one declaration, so their elements
||| pair up whatever the order. Each intrinsic must have exactly one extern.
|||
||| The OS services are found the same way, by their enumeration
||| (`Native.Service`): each extern, `PortTy (port c)`, and the function of
||| the platform's module that implements it, of the same type, paired by
||| their constructor.
|||
||| The routines are found the same way (`Native.Routine`), each a function
||| `PortTy (port c)` of the runtime, and the string routines
||| (`Native.Types.StringRoutine`) in the string encoding's module. The
||| string routines the runtime's own code calls each have an extern, as a
||| service does, paired with the encoding's function by their constructor.
|||
||| The backend's primitives are found the same way (`Native.Primitive`),
||| each a definition `FunctionTy (signature c)` of a module of
||| `Native.Primitive`, at most one of each: a program that imports none
||| uses none. The tables (`Native.Table`) are found by their type too,
||| `Table lo hi r`, wherever they are, with their ranges.
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Native.Codegen.Linkage.Routine` says what it is).
module Native.Codegen.Linkage.Realised

import Native.Codegen.Linkage.OSService
import Native.Codegen.Linkage.RuntimeModule

import Core.Case.CaseTree
import Core.Context
import Core.Context.Context
import Core.Core
import Core.Env
import Core.Name
import Core.Name.Namespace
import Core.Name.Scoped
import Core.Normalise
import Core.TT
import Core.TT.Primitive
import Core.TT.Term
import Core.Value
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.Zippable
import Native.Codegen.Platform
import Native.Intrinsic
import Native.Primitive
import Native.Routine
import Native.Service
import Native.Types.Enc as Types
import Native.Types.IntegerRoutine as Types
import Native.Types.StringRoutine as Types

%default covering

||| The contract's entries, as the loaded runtime realises them.
public export
record Realised where
  constructor MkRealised
  ||| Each routine of the runtime's core, with the function that is it.
  routines : List (Name, Routine)
  ||| Each routine of the string encoding's module, with the function that
  ||| is it, if the runtime has a module for the encoding.
  strings : Maybe (List (Name, Types.StringRoutine))
  ||| Each routine of the bignum encoding's module, with the function that is
  ||| it, if the runtime has a module for the encoding.
  integers : Maybe (List (Name, Types.IntegerRoutine))
  ||| Each inline extern, with the intrinsic it is.
  externs : SortedMap Name Intrinsic
  ||| Each extern bound to a function the program's choices pick: each OS
  ||| service's, with the platform's function for it, and each of the
  ||| string encoding's (`StringRoutine`'s text), with the encoding's.
  services : SortedMap Name Name
  ||| Each of the backend's primitives the context defines, with the
  ||| primitive it is.
  primitives : SortedMap Name Primitive
  ||| Each table the context defines, with its range, `lo` to `hi`.
  tables : SortedMap Name (Int, Int)

||| A definition of the root of a module.
in' : Namespace -> String -> Name
in' ns n = NS ns (UN (Basic n))

||| The definitions the context keeps whose type is the port of a
||| constructor of a contract's enumeration, `f (port c)` for a head `f` of
||| `heads`, or its signature, `f (signature c)`,
||| each with its constructor's name and the code generator's own
||| constructor; exactly one of each if `required`, else at most one, or
||| which have none or more. The constructors are the enumeration's list's
||| (`listName`, in the module `contract`): its term in the context and the
||| code generator's copy of it (`own`) are one declaration, so their
||| elements pair up whatever the order. A context without the list has
||| none of them, which only an enumeration not `required` may.
entries : {auto c : Ref Ctxt Defs} -> (required : Bool) -> (contract, listName : String) ->
          (own : List a) -> (heads : List Name) ->
          (keep : Name -> GlobalDef -> Bool) -> Core (Either String (List (Name, Name, a)))
entries required contract listName own heads keep = do
  defs <- get Ctxt
  Just lg <- lookupCtxtExact (in' ns listName) (gamma defs)
    | Nothing =>
      pure (if required then Left ("the runtime has no " ++ show (in' ns listName)) else Right [])
  listed <- case definition lg of
    PMDef _ _ (STerm _ tm) _ _ => elements <$> toFullNames tm
    _ => pure []
  let byConstructor = fromList (zip listed own)
  found <- catMaybes <$> traverse (entry defs byConstructor) !(allNames (gamma defs))
  let problems = mapMaybe (\c => case length (filter (\(_, c', _) => c' == c) found) of
                                    1 => Nothing
                                    0 => if required then Just (show c ++ " has none") else Nothing
                                    k => Just (show c ++ " has " ++ show k)) listed
  pure (if null problems then Right found else Left (concat (intersperse "; " problems)))
  where
    ns : Namespace
    ns = mkNamespace contract

    -- the elements of a list's term, `(::) {a} x xs` down to `Nil`
    elements : Term vars -> List Name
    elements tm = case getFnArgs tm of
      (Ref _ _ _, [_, Ref _ _ x, rest]) => x :: elements rest
      _ => []

    -- the constructor a type is the port of, if it is one
    typePort : Term vars -> Maybe Name
    typePort ty = case getFnArgs ty of
      (Ref _ _ f, args) =>
        if not (f `elem` heads) then Nothing
        else case reverse args of
          (arg :: _) => case getFnArgs arg of
            (Ref _ _ p, [Ref _ _ c]) =>
              if p == in' ns "port" || p == in' ns "signature" then Just c else Nothing
            _ => Nothing
          [] => Nothing
      _ => Nothing

    -- a definition of the port of a constructor, with it
    entry : Defs -> SortedMap Name a -> Name -> Core (Maybe (Name, Name, a))
    entry defs byConstructor n = do
      Just g <- lookupCtxtExact n (gamma defs)
        | Nothing => pure Nothing
      n' <- toFullNames n
      if not (keep n' g) then pure Nothing else do
        ty <- toFullNames (type g)
        pure $ do
          c <- typePort ty
          i <- lookup c byConstructor
          pure (n', c, i)

||| The backend's primitives the context defines (`Native.Primitive`), each
||| by its type, `FunctionTy (signature c)`, in a module of
||| `Native.Primitive`: at most one of each.
primitives : {auto c : Ref Ctxt Defs} -> Core (Either String (List (Name, Name, Primitive)))
primitives =
  entries False "Native.Primitive" "allPrimitives" Primitive.allPrimitives [functionTy] inPrimitive
  where
    functionTy : Name
    functionTy = in' (mkNamespace "Native.Primitive") "FunctionTy"

    inPrimitive : Name -> GlobalDef -> Bool
    inPrimitive (NS ns _) _ = ns /= mkNamespace "Native.Primitive"
      && isParentOf (mkNamespace "Native.Primitive") ns
    inPrimitive _ _ = False

||| The tables the context defines (`Native.Table`), each by its type,
||| `Table lo hi r`, with its range if `lo` and `hi` reduce to `Int`s.
tables : {auto c : Ref Ctxt Defs} -> Core (List (Name, Maybe (Int, Int)))
tables = do
  defs <- get Ctxt
  catMaybes <$> traverse (table defs) !(allNames (gamma defs))
  where
    table : Defs -> Name -> Core (Maybe (Name, Maybe (Int, Int)))
    table defs n = do
      Just g <- lookupCtxtExact n (gamma defs)
        | Nothing => pure Nothing
      let (Ref _ _ f, [lo, hi, _]) = getFnArgs (type g)
        | _ => pure Nothing
      if !(toFullNames f) /= in' (mkNamespace "Native.Table") "Table" then pure Nothing else do
        lo' <- normaliseOpts withAll defs Env.empty lo
        hi' <- normaliseOpts withAll defs Env.empty hi
        n' <- toFullNames n
        pure $ Just $ case (lo', hi') of
          (PrimVal _ (I l), PrimVal _ (I h)) => (n', Just (l, h))
          _ => (n', Nothing)

||| The definitions the flat translation takes a call of as a primitive's:
||| the backend's primitives and the tables the context defines; none of a
||| primitive where there are two of one, which `realise` reports.
export
flatPrimitives : Ref Ctxt Defs -> Core (List Name)
flatPrimitives c = do
  ps <- either (const []) (map (\(n, _, _) => n)) <$> primitives
  ts <- map fst <$> tables
  pure (ps ++ ts)

||| The contract as the loaded runtime realises it, for the platform and the
||| encodings, or what is missing.
export
realise : {auto c : Ref Ctxt Defs} -> Platform -> Types.Enc -> Core (Either String Realised)
realise platform enc = do
  Right rs <- entries True "Native.Routine" "allRoutines" Routine.allRoutines [portTy] runtimeOwn
    | Left e => pure (Left ("the runtime's routines: " ++ e))
  ss <- case RuntimeModule.stringModule enc.string of
    Just ns => map (map Just) (entries True "Native.Types.StringRoutine" "allStringRoutines"
                                 Types.StringRoutine.allStringRoutines [portTy] (inModule ns))
    Nothing => pure (Right Nothing)
  let Right ss' = ss
    | Left e => pure (Left ("the string encoding's routines: " ++ e))
  is <- case RuntimeModule.bignumModule enc of
    Just ns => map (map Just) (entries True "Native.Types.IntegerRoutine" "allIntegerRoutines"
                                 Types.IntegerRoutine.allIntegerRoutines [portTy] (inModule ns))
    Nothing => pure (Right Nothing)
  let Right is' = is
    | Left e => pure (Left ("the bignum encoding's routines: " ++ e))
  Just platformNs <- pure (OSService.platformModule platform)
    | Nothing => pure (Left ("the platform " ++ show platform ++ " has no OS services"))
  Right intrinsics <- entries True "Native.Intrinsic" "allIntrinsics" Intrinsic.allIntrinsics
    [portTy] isExtern
    | Left e => pure (Left ("the runtime's inline externs: " ++ e))
  Right serviceExterns <- entries True "Native.Service" "allServices" Service.allServices [portTy]
    isExtern
    | Left e => pure (Left ("the runtime's OS services: " ++ e))
  Right serviceFunctions <- entries True "Native.Service" "allServices" Service.allServices [portTy]
    (inModule platformNs)
    | Left e => pure (Left ("the platform's OS services: " ++ e))
  Right textExterns <- entries False "Native.Types.StringRoutine" "allStringRoutines"
    Types.StringRoutine.allStringRoutines [portTy] isExtern
    | Left e => pure (Left ("the runtime's externs of the string encoding: " ++ e))
  Right prims <- primitives
    | Left e => pure (Left ("the backend's primitives: " ++ e))
  ts <- tables
  let [] = mapMaybe (\(n, r) => maybe (Just n) (const Nothing) r) ts
    | (n :: _) =>
      pure (Left ("the table " ++ show n ++ " has a range that does not reduce to two Ints"))
  let externs = fromList [ (n, i) | (n, _, i) <- intrinsics ]
      services =
        fromList ([ (x, f) | (x, c, _) <- serviceExterns, (f, c', _) <- serviceFunctions, c == c' ]
                           ++ [ (x, f) | (x, c, _) <- textExterns,
                               (f, c', _) <- fromMaybe [] ss', c == c' ])
  pure
    (Right
      (MkRealised (pairs rs) (map pairs ss') (map pairs is') externs services
       (fromList (pairs prims))
                           (fromList (mapMaybe (\(n, r) => (n,) <$> r) ts))))
  where
    portTy : Name
    portTy = in' (RuntimeModule.runtimeModule "PortTy") "PortTy"

    isExtern : Name -> GlobalDef -> Bool
    isExtern _ g = case definition g of
      ExternDef _ => True
      _ => False

    inModule : Namespace -> Name -> GlobalDef -> Bool
    inModule ns (NS ns' _) _ = ns' == ns
    inModule _ _ _ = False

    runtimeOwn : Name -> GlobalDef -> Bool
    runtimeOwn (NS ns _) _ = RuntimeModule.inRuntime ns
    runtimeOwn _ _ = False

    -- each entry's definition, with the code generator's constructor
    pairs : List (Name, Name, a) -> List (Name, a)
    pairs es = [ (n, x) | (n, _, x) <- es ]
